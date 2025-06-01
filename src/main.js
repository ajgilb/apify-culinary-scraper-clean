import { CheerioCrawler, KeyValueStore, RequestQueue, log, Dataset } from 'crawlee';
import cheerio from 'cheerio';
import fetch from 'node-fetch';
import { Actor } from 'apify';
import pkg from 'pg';
import { Resend } from 'resend'; // Added for email notifications
const { Pool } = pkg;

// Load environment variables from .env files when running locally
import dotenv from 'dotenv';
import fs from 'fs';
import path from 'path';

if (!process.env.APIFY_IS_AT_HOME) {
    // Try to load from .env.local first (preferred for local development)
    const localEnvPath = path.resolve(process.cwd(), '.env.local');
    const defaultEnvPath = path.resolve(process.cwd(), '.env');

    if (fs.existsSync(localEnvPath)) {
        dotenv.config({ path: localEnvPath });
        log.info('Loaded environment variables from .env.local file');
    } else if (fs.existsSync(defaultEnvPath)) {
        dotenv.config();
        log.info('Loaded environment variables from .env file');
    } else {
        log.warning('No .env or .env.local file found');
    }
}

// Configuration
let TEST_MODE = true;  // Running in production mode
let TEST_JOB_LIMIT = 5;
let EXPORT_DATA = true;

const BATCH_SIZE = 9;
const BASE_URL = 'https://culinaryagents.com';
const MAX_CELL_LENGTH = 50000;

// --- BATCH EXPORT SETTINGS ---
const EXPORT_BATCH_SIZE = 10; // Export every 10 jobs
let exportBatch = [];
// let loggedIn = false; // REMOVED login flag

// PostgreSQL Configuration
const connectionString = 'postgresql://postgres.mbaqiwhkngfxxmlkionj:Relham12%3F@aws-0-us-west-1.pooler.supabase.com:6543/postgres';
const pool = new Pool({
    connectionString,
    ssl: {
        rejectUnauthorized: false
    }
});

// Add this after the pool configuration
pool.on('error', (err) => {
    console.error('Unexpected error on idle client', err);
});

// Create a global array to store jobs - used for global state only
let allProcessedJobs = [];

// Contact collection has been disabled - Hunter.io API removed
// All other data collection (domains, LinkedIn, company info) is preserved

// Google Sheets Configuration
// const SHEET_ID = '1hFgWma-Jjq31Tb2yn9U8PWgfC8KOpp0njdg3c1JEjsI'; // Your Sheet ID
// const SHEET_NAME = 'Sheet1'; // The name of the sheet to read from and append to
// const SHEET_RANGE = 'Sheet1!A1'; // Adjust if needed (Likely only needed for specific reads/writes, not append)

// Exclusion list
const EXCLUDED_COMPANIES = new Set([
    "Alliance Personnel", "August Point Advisors", "Bon Appetit", "Capital Restaurant Associates",
    "Chartwells", "Compass", "CORE Recruitment", "EHS Recruiting", "Empowered Hospitality",
    "Eurest", "Goodwin Recruiting", "HMG Plus - New York", "LSG Sky Chefs", "Major Food Group",
    "Measured HR", "One Haus", "Patrice & Associates", "Persone NYC", "Playbook Advisors",
    "Restaurant Associates", "Source One Hospitality", "Ten Five Hospitality",
    "The Goodkind Group", "Tuttle Hospitality", "Willow Tree Recruiting",
    // Adding Washington variants
    "washington", "washington dc", "washington d.c.", "washington d c"
].map(name => name.toLowerCase()));

// List of partial match exclusions (for companies with variations like "Whole Foods Market", etc.)
const PARTIAL_EXCLUSIONS = [
    "whole foods"
].map(name => name.toLowerCase());

// Force fresh companies constant removed - contact collection disabled

// Helper functions
const timeout = (ms) => new Promise((_, reject) => setTimeout(() => reject(new Error(`Operation timed out after ${ms}ms`)), ms));
const delay = (ms) => new Promise(resolve => setTimeout(resolve, ms));
const now = () => new Date().toISOString();

// Helper function to clean special characters but keep basic punctuation
function cleanSpecialCharacters(text) {
    if (!text) return '';
    // Keep only alphanumeric, spaces, and basic punctuation
    return text.replace(/[^\w\s.,&'-]/g, '');
}

// Email filtering constants removed - contact collection disabled

// Job title sorting priority - ordered from highest to lowest priority
const TITLE_PRIORITY = [
    // HR & Talent Acquisition roles (absolute top priority)
    'chief people officer', 'chief human resources officer', 'chro',
    'head of hr', 'head of human resources', 'head of people', 'head of talent',
    'hr director', 'human resources director', 'people director', 'talent director', 'talent acquisition director',
    'vp of hr', 'vp of human resources', 'vp of people', 'vp of talent', 'vp of talent acquisition',
    'people operations', 'people ops', 'talent operations',
    'hr manager', 'human resources manager', 'people manager', 'talent manager', 'talent acquisition manager',
    'hr specialist', 'human resources specialist', 'people specialist', 'talent specialist',
    'recruiter', 'talent recruiter', 'technical recruiter', 'executive recruiter',
    'hr', 'human resources', 'people', 'talent', 'talent acquisition',

    // C-level executives
    'ceo', 'chief executive officer',
    'president',
    'coo', 'chief operating officer',
    'chief people officer', 'chief talent officer',
    'chief',

    // Regional/Area Leadership (higher than local managers)
    'regional director', 'area director', 'district director',
    'regional manager', 'area manager', 'district manager',
    'regional', 'area', 'district',

    // Directors
    'director of operations', 'operations director',
    'director of hr', 'director of human resources', 'director of people',
    'director of recruiting', 'recruiting director',
    'director',

    // Other executives/management
    'vice president', 'vp',
    'general manager', 'gm',
    'manager',
    'executive',
    'founder', 'owner', 'partner',

    // Other terms (lowest priority)
    'recruiting', 'hiring', 'employment', 'personnel'
];

function getTitlePriority(title) {
    if (!title) return TITLE_PRIORITY.length + 1;

    const lowerTitle = title.toLowerCase();
    let highestPriority = TITLE_PRIORITY.length + 1;

    // First check for exact matches (highest precedence)
    const exactMatchIndex = TITLE_PRIORITY.indexOf(lowerTitle);
    if (exactMatchIndex !== -1) {
        return exactMatchIndex;
    }

    // Special case handling for HR/Talent/People roles with different word order
    // This specifically targets cases like "Manager of HR" vs "HR Manager"
    const roleTypes = [
        { key: "hr", alt: "human resources" },
        { key: "talent", alt: "talent acquisition" },
        { key: "people", alt: "people operations" }
    ];

    const levelTypes = [
        { key: "manager", alt: "manager of" },
        { key: "director", alt: "director of" },
        { key: "vp", alt: "vice president" },
        { key: "head", alt: "head of" },
        { key: "chief", alt: "chief" }
    ];

    // Check all combinations of role + level to handle different word orders
    for (const role of roleTypes) {
        for (const level of levelTypes) {
            // Check different word orders:
            // 1. "{role} {level}" (e.g., "HR Manager")
            // 2. "{level} of {role}" (e.g., "Manager of HR")
            // 3. "{level}, {role}" (e.g., "Manager, Human Resources")

            const patternA = `${role.key} ${level.key}`;
            const patternB = `${level.key} of ${role.key}`;
            const patternC = `${level.key}, ${role.key}`;

            const patternD = `${role.alt} ${level.key}`;
            const patternE = `${level.key} of ${role.alt}`;
            const patternF = `${level.key}, ${role.alt}`;

            const patternG = `${level.alt} ${role.key}`;
            const patternH = `${level.alt} ${role.alt}`;

            // Find the standard form in our priority list
            let standardForm = `${role.key} ${level.key}`;
            let standardIndex = TITLE_PRIORITY.indexOf(standardForm);

            if (standardIndex === -1) {
                standardForm = `${role.alt} ${level.key}`;
                standardIndex = TITLE_PRIORITY.indexOf(standardForm);
            }

            // If we have a standard form for this role+level combo
            if (standardIndex !== -1) {
                // Check if any of our patterns match the title
                if (lowerTitle.includes(patternA) || lowerTitle.includes(patternB) ||
                    lowerTitle.includes(patternC) || lowerTitle.includes(patternD) ||
                    lowerTitle.includes(patternE) || lowerTitle.includes(patternF) ||
                    lowerTitle.includes(patternG) || lowerTitle.includes(patternH)) {

                    highestPriority = standardIndex;
                    return highestPriority; // Return immediately for these special matches
                }
            }
        }
    }

    // Special handling for VP and Head titles
    if ((lowerTitle.includes('vp') || lowerTitle.includes('vice president')) &&
        (lowerTitle.includes('hr') || lowerTitle.includes('human resources') ||
         lowerTitle.includes('people') || lowerTitle.includes('talent'))) {

        // Find the best matching VP term
        for (let i = 0; i < TITLE_PRIORITY.length; i++) {
            const term = TITLE_PRIORITY[i];
            if (term.startsWith('vp of ') && lowerTitle.includes(term.substring(6))) {
                highestPriority = i;
                return highestPriority;
            }
        }
    }

    // Then look for substring matches, prioritizing longer matches first
    for (let i = 0; i < TITLE_PRIORITY.length; i++) {
        const priorityTerm = TITLE_PRIORITY[i];

        // For multi-word terms, check if all words appear in the title
        // This helps match "Director of Human Resources" with "Human Resources Director"
        if (priorityTerm.includes(' ')) {
            const words = priorityTerm.split(' ');
            if (words.every(word => lowerTitle.includes(word))) {
                highestPriority = i;
                break;
            }
        }

        // Special handling for "chief" to avoid matching "chief cook" as "chief"
        if (priorityTerm === 'chief' && lowerTitle.includes('chief')) {
            const isRealChief = /(^|\s)chief($|\s|,)/.test(lowerTitle) ||
                                lowerTitle.includes('chief ') &&
                                !lowerTitle.includes('chief cook');
            if (isRealChief) {
                highestPriority = i;
                break;
            }
        }
        // Then check for standard includes for other terms
        else if (lowerTitle.includes(priorityTerm)) {
            highestPriority = i;
            break;
        }
    }

    return highestPriority;
}

function truncateText(text, maxLength = MAX_CELL_LENGTH) {
    if (!text) return '';
    return text.length > maxLength ? text.substring(0, maxLength - 3) + '...' : text;
}

function cleanCompanyName(input) {
    if (!input || typeof input !== 'string') return '';

    // Keep the full name for companies with multiple words
    let cleaned = input
        // Remove common business entity suffixes
        .replace(/\s+(restaurant|bar|café|cafe|grill|bistro|tavern|kitchen|hospitality|group|llc|inc|corporation)\b/gi, '')
        // Remove location markers
        .replace(/\s+[,-]\s+.*$/, '')
        .trim();

    return cleaned || input;
}

function cleanLocationText(input) {
    if (!input || typeof input !== 'string') return '';

    const original = input;
    let cleaned = input
        // Fix missing spaces between words (e.g., "CompanyCity" -> "Company City")
        .replace(/([a-z])([A-Z])/g, '$1 $2')
        // Fix missing spaces between company names and cities (e.g., "CompanyNew York" -> "Company New York")
        .replace(/([a-zA-Z])([A-Z][a-z]+,?\s*[A-Z]{2})/g, '$1 $2')
        // Fix missing spaces before state abbreviations (e.g., "CityNY" -> "City NY")
        .replace(/([a-z])([A-Z]{2}$)/g, '$1 $2')
        // Fix missing spaces before common multi-word city names
        .replace(/([a-z])(New York|Los Angeles|San Francisco|Las Vegas|San Diego|San Antonio|San Jose|Kansas City|St\. Louis|Virginia Beach|Colorado Springs|Long Beach|St\. Petersburg|North Las Vegas|Salt Lake City|Fort Lauderdale|Grand Rapids|Cape Coral|Garden Grove|Newport News|Fort Wayne|St\. Paul)/gi, '$1 $2')
        // Clean up multiple spaces
        .replace(/\s+/g, ' ')
        .trim();

    // Log when location text was cleaned
    if (cleaned !== original) {
        console.info(`LOCATION CLEANED: "${original}" → "${cleaned}"`);
    }

    return cleaned || input;
}

// Enhanced company name extractor focused on accurate company name identification
// Exported for testing
export function parseCompanyAndLocation(rawName) {
    if (!rawName || rawName === 'Unknown') {
        return { name: 'Unknown', location: '' };
    }

    log.info(`Parsing company name from: "${rawName}"`);

    // List of generic industry terms that shouldn't be treated as company names on their own
    const genericTerms = [
        'restaurant group', 'hospitality group', 'restaurant', 'hospitality',
        'group', 'consulting', 'management', 'restaurant consulting',
        'hospitality consulting', 'food and beverage', 'f&b',
        'bar', 'cafe', 'bistro', 'tavern', 'eatery', 'catering',
        'culinary', 'culinary group', 'bakery', 'dining', 'dining group',
        'restaurant management', 'hospitality management', 'fine dining'
    ];

    // Common locations that might appear without proper spacing
    // Also used to detect if a string is just a location name
    // Expanded list based on US major cities and common state abbreviations
    // Source: https://github.com/kelvins/US-Cities-Database
    const commonLocations = [
        // Major cities
        'New York', 'Los Angeles', 'Chicago', 'Houston', 'Phoenix', 'Philadelphia',
        'San Antonio', 'San Diego', 'Dallas', 'San Jose', 'Austin', 'Jacksonville',
        'Fort Worth', 'Columbus', 'Indianapolis', 'Charlotte', 'San Francisco',
        'Seattle', 'Denver', 'Washington', 'Boston', 'El Paso', 'Nashville',
        'Detroit', 'Oklahoma City', 'Portland', 'Las Vegas', 'Memphis', 'Louisville',
        'Baltimore', 'Milwaukee', 'Albuquerque', 'Tucson', 'Fresno', 'Sacramento',
        'Kansas City', 'Miami', 'Omaha', 'Raleigh', 'Oakland', 'Minneapolis',
        'Tulsa', 'Cleveland', 'Wichita', 'Arlington', 'New Orleans', 'Bakersfield',
        'Tampa', 'Honolulu', 'Aurora', 'Anaheim', 'Santa Ana', 'St. Louis',
        'Pittsburgh', 'Cincinnati', 'Henderson', 'Riverside', 'St. Paul',

        // NYC boroughs
        'Manhattan', 'Brooklyn', 'Queens', 'The Bronx', 'Staten Island', 'NYC',

        // Common state abbreviations
        'NY', 'LA', 'IL', 'CA', 'FL', 'TX', 'GA', 'MA', 'SF', 'DC', 'PA',
        'WA', 'CO', 'AZ', 'TN', 'MO', 'OR', 'NV', 'KY', 'IN', 'OH', 'NC',
        'MI', 'MD', 'VA', 'NJ', 'MN'
    ];

    // List of known restaurant group keywords - used to identify company names in complex strings
    const restaurantKeywords = [
        'restaurants by', 'restaurants of', 'restaurant group', 'hospitality group',
        'dining group', 'food group', 'culinary group', 'chef', 'kitchen',
        'bistro', 'cafe', 'dining', 'eatery', 'tavern', 'grill', 'restaurant'
    ];

    // Step 0: Early check for excluded companies regardless of formatting
    // This catches cases like "Whole FoodsAustin" where spacing is missing
    const cleanedRawName = cleanSpecialCharacters(rawName); // Remove special characters
    const normalizedRawName = cleanedRawName.toLowerCase().replace(/\s+/g, '');

    // Check for excluded companies with normalized spaces
    for (const excludedName of PARTIAL_EXCLUSIONS) {
        const normalizedExcludedName = excludedName.replace(/\s+/g, '');
        if (normalizedRawName.includes(normalizedExcludedName)) {
            log.info(`Early exclusion match for "${excludedName}" in "${rawName}" (normalized: "${normalizedRawName}")`);
            return { name: `Excluded: ${excludedName}`, location: '' };
        }
    }

    // Check for exact matches in the exclusion list
    const rawNameLower = cleanedRawName.toLowerCase();
    if (Array.from(EXCLUDED_COMPANIES).some(excluded => rawNameLower.includes(excluded))) {
        log.info(`Early exact exclusion match in "${rawName}"`);
        return { name: 'Excluded', location: '' };
    }

    // Step 1: Check if the input starts with a location
    // This is a common pattern in listings like "New York, NY • Restaurant Group"
    const startsWithLocation = commonLocations.some(loc =>
        rawNameLower.startsWith(loc.toLowerCase())
    );

    if (startsWithLocation && rawName.includes('•')) {
        // If it starts with a location and has industry classification, it's likely not a company
        log.info(`Input starts with location and contains bullet point: "${rawName}"`);
        return { name: 'Unknown', location: '' };
    }

    // Step 2: Split by bullet to isolate the company part
    // This often contains generic industry categorization
    let namePart = cleanSpecialCharacters(rawName.split('•')[0].trim());

    // Step 2.5: Look for words that are run together based on case changes
    // Example: "HourWashington" should become "Hour Washington"

    // First check for cities that are run together with previous words
    // We'll check for all cities in our commonLocations list
    for (const location of commonLocations) {
        // Only check locations that are at least 5 characters long to avoid false positives
        if (location.length >= 5 && namePart.includes(location) && !namePart.includes(' ' + location)) {
            // Find the city without a space before it - use word boundary for the beginning of the city name
            // This is critical for cases like "HourWashington" where we want to match the W in Washington
            const cityPattern = new RegExp(`([a-z])${location}`, 'i');
            if (cityPattern.test(namePart)) {
                // Check for Hour + Washington specifically, which is a common pattern
                if (namePart.match(/Hour${location}/i)) {
                    log.info(`Found special case Hour${location} pattern, fixing...`);
                    namePart = namePart.replace(new RegExp(`Hour${location}`, 'i'), `Hour ${location}`);
                } else {
                    namePart = namePart.replace(cityPattern, `$1 ${location}`);
                }
                log.info(`Fixed missing space before city name: "${namePart}"`);
            }
        }
    }

    // Look for common word endings followed by capitalized location names,
    // but don't apply to "Barbecue" or restaurant names with locations like "- Miami"
    // Check for these exceptions first
    if (!namePart.includes('Barbecue') && !namePart.includes(' - ')) {
        const wordBoundaryPattern = /(\b(?:hour|room|cafe|bar|club|bistro|grill|tap|lounge|den|pub|inn|shop|house|bakery))([A-Z][a-z]+)/i;

        // Check for other common word boundaries
        const wordBoundaryMatch = namePart.match(wordBoundaryPattern);
        if (wordBoundaryMatch) {
            // Insert a space between the words
            namePart = namePart.replace(wordBoundaryPattern, '$1 $2');
            log.info(`Fixed missing space between words: "${namePart}"`);
        }
    }

    // Step 3: Special handling for known edge cases and patterns
    let extractedFromKeywords = false;

    // SPECIAL CHECK FOR ALL CAPS RESTAURANT GROUP PATTERNS
    // This handles "MARCUS SAMUELSSON RESTAURANT GROUP" type patterns first
    if (/^[A-Z\s.'&]+\s+RESTAURANT\s+GROUP$/i.test(namePart) ||
        /^[A-Z\s.'&]+\s+HOSPITALITY\s+GROUP$/i.test(namePart) ||
        /^[A-Z\s.'&]+\s+FINE\s+DINING$/i.test(namePart) ||
        /^[A-Z\s.'&]+\s+CULINARY\s+GROUP$/i.test(namePart)) {
        // This is a full restaurant group name in all caps - preserve it as is
        log.info(`Detected full restaurant/hospitality group name, preserving as is: "${namePart}"`);
        extractedFromKeywords = true;
        // Skip further processing to ensure this name is kept intact
    }

    // Special case for company names ending with common terms that would otherwise be excluded
    // This ensures we keep "MARCUS SAMUELSSON RESTAURANT GROUP" and "Blue Hill Fine Dining"
    if (!extractedFromKeywords) {
        const excludedEndingPatterns = [
            /^(.+\s+)restaurant\s+group$/i,
            /^(.+\s+)hospitality\s+group$/i,
            /^(.+\s+)fine\s+dining$/i,
            /^(.+\s+)culinary\s+group$/i,
            /^(.+\s+)dining\s+group$/i,
            /^(.+\s+)restaurant\s+management$/i,
            /^(.+\s+)hospitality\s+management$/i
        ];

        // Check if the name matches any of these patterns
        for (const pattern of excludedEndingPatterns) {
            if (pattern.test(namePart)) {
                // This is a proper company name that ends with a term we'd normally exclude
                // Match will be something like ["Marcus Samuelsson Restaurant Group", "Marcus Samuelsson "]
                // We want to keep the full name
                extractedFromKeywords = true;
                log.info(`Detected proper company name with common ending term, preserving: "${namePart}"`);
                break;
            }
        }
    }

    // Special case for GroupNYC and similar patterns
    if (!extractedFromKeywords && namePart.match(/Group\s*NYC\b/i)) {
        namePart = "Group NYC Hospitality";
        extractedFromKeywords = true;
        log.info(`Detected GroupNYC pattern, using: "${namePart}"`);
    }

    // Example: "P.M. Pastry Sous Chef abc V Restaurants by JorgesNew York"
    // Look for restaurant keywords in the string and prioritize that as the company name
    if (!extractedFromKeywords) {
        for (const keyword of restaurantKeywords) {
            const index = namePart.toLowerCase().indexOf(keyword);
            // Only extract if not at the beginning - prevents extracting just "Restaurant Group"
            // from "Marcus Samuelsson Restaurant Group"
            if (index > 3) {
                // Found a keyword - extract from here to either the end or next location indicator
                // But first check if this is a full restaurant name (don't extract just the generic part)
                const beforeKeyword = namePart.substring(0, index).trim();
                if (beforeKeyword.split(/\s+/).length >= 2) {
                    // If there are at least 2 words before the keyword,
                    // like "Marcus Samuelsson" in "Marcus Samuelsson Restaurant Group",
                    // then keep the full name, don't extract just "Restaurant Group"
                    continue;
                }

                const startIndex = index;
                let endIndex = namePart.length;

                // Look for location markers to determine where the company name ends
                for (const location of commonLocations) {
                    const locationIndex = namePart.indexOf(location, startIndex);
                    if (locationIndex > startIndex && locationIndex < endIndex) {
                        endIndex = locationIndex;
                        break;
                    }
                }

                // Extract the potential company name
                const potentialCompany = namePart.substring(startIndex, endIndex).trim();

                // Check if it's a generic term on its own or very close to it
                // We'll consider it too generic if it's exactly a generic term OR
                // if it's a generic term with just one or two extra words
                const potentialLower = potentialCompany.toLowerCase();
                const isExactGenericTerm = genericTerms.includes(potentialLower) ||
                                          potentialLower === 'restaurant group' ||
                                          potentialLower === 'fine dining';

                // Count words - if it's a generic term plus just 1 word, it might still be too generic
                const wordCount = potentialCompany.split(/\s+/).filter(w => w.length > 1).length;
                const isGenericPlusOneWord = wordCount <= 3 &&
                    (potentialLower.endsWith(' restaurant group') ||
                    potentialLower.endsWith(' fine dining') ||
                    potentialLower.endsWith(' hospitality group') ||
                    potentialLower.endsWith(' restaurant') ||
                    potentialLower.endsWith(' hospitality'));

                if (isExactGenericTerm || isGenericPlusOneWord) {
                    // Skip if it's just a generic term or too close to one
                    log.info(`Would extract generic-like term "${potentialCompany}" - skipping`);
                    continue;
                }

                // If it's substantial (not just the keyword itself), use it
                if (potentialCompany.length > keyword.length + 2) {
                    log.info(`Extracted restaurant name using keyword "${keyword}": "${potentialCompany}"`);
                    namePart = potentialCompany;
                    extractedFromKeywords = true;
                    break;
                }
            }
        }
    }

    // Step 4: Handle missing spaces before location identifiers (if we haven't found a better match yet)
    // This helps with cases like "Seaport Entertainment GroupNew York, NY"
    if (!extractedFromKeywords) {
        let locationFound = false;

        // Sort locations by length (descending) to match longest locations first
        // This helps avoid partial matches like "NY" in "Georges"
        const sortedLocations = [...commonLocations].sort((a, b) => b.length - a.length);

        for (const location of sortedLocations) {
            // Skip very short location names (2 chars) for this pattern match to avoid false positives
            // These will be handled by comma separation instead
            if (location.length <= 2) continue;

            // Create a regex that looks for a lowercase or uppercase letter followed immediately by the location
            // This suggests a missing space between company name and location
            const locationRegex = new RegExp(`([a-zA-Z])(${location}\\b)`, 'i');
            const match = namePart.match(locationRegex);

            if (match) {
                // We found a missing space before a known location
                const locationStart = match.index + 1; // +1 because of the capturing group

                // Check if we're in the middle of a word - avoid splitting "Georges" just because it has "GE"
                const prevChar = namePart.charAt(match.index);
                const nextCharAfterMatch = namePart.charAt(match.index + match[0].length);

                // Only split if it's at a word boundary or end of string
                const isWordBoundary = nextCharAfterMatch === '' || /\s|,|\./.test(nextCharAfterMatch);

                if (isWordBoundary) {
                    namePart = namePart.substring(0, locationStart).trim();
                    log.info(`Fixed missing space before location: "${namePart}"`);
                    locationFound = true;
                    break; // Stop after finding the first location match
                }
            }
        }

        // Step 5: Handle comma-separated parts (typically location markers)
        // In format "Company Name, Location"
        if (!locationFound) {
            const commaIndex = namePart.lastIndexOf(',');
            if (commaIndex !== -1) {
                // Check if there are multiple commas (like "Company Name, Location, State")
                const firstPart = namePart.substring(0, commaIndex).trim();

                // If the part before the comma contains another comma, we might have "Name, Location, State"
                // In this case, we want to get the name part only
                const earlierCommaIndex = firstPart.lastIndexOf(',');
                if (earlierCommaIndex !== -1) {
                    namePart = firstPart.substring(0, earlierCommaIndex).trim();
                    log.info(`Removed multiple location parts: "${namePart}"`);
                } else {
                    namePart = firstPart;
                    log.info(`Removed location after comma: "${namePart}"`);
                }
            }
        }
    }

    // Step 6: Fix any camelCase issues in the name
    // This handles cases where words are run together like "GroupNew"
    // Special handling for "NYC" and "SoHo" which should not be split
    if (!namePart.includes("NYC") && !namePart.includes("SoHo")) {
        namePart = namePart.replace(/([a-z])([A-Z])/g, '$1 $2');
    }

    // Step 7: Try to identify and extract the most likely company name portion
    // Look for common patterns in the remaining string
    if (!extractedFromKeywords && namePart.includes(' by ')) {
        // Format like "Restaurants by Jorge"
        const byIndex = namePart.indexOf(' by ');
        if (byIndex > 0) {
            namePart = namePart.substring(byIndex - 11 >= 0 ? byIndex - 11 : 0).trim();
            log.info(`Extracted company using 'by' indicator: "${namePart}"`);
        }
    }

    // Step 8: Clean up business entity suffixes
    // But PRESERVE important terms like "Group" in company names
    const originalName = namePart;
    namePart = namePart
        .replace(/\s+(LLC|Inc|Corporation|Corp|Co\.|Co)\.?$/i, '')
        .trim();

    // Only remove trailing generic terms if they're not part of a multi-word company name
    // This preserves "Hospitality Group" or "Restaurant Group" in proper names
    if (!/(square|food|hospitality|culinary|entertainment)\s+group$/i.test(namePart)) {
        namePart = namePart
            .replace(/\s+(restaurant|bar|café|cafe|grill|bistro|tavern|kitchen)$/i, '')
            .trim();
    }

    // Step 9: Remove any job title prefixes that might remain
    // Common job title patterns at the beginning
    const jobTitlePrefixes = [
        'chef', 'sous chef', 'pastry chef', 'head chef', 'executive chef',
        'general manager', 'assistant manager', 'manager', 'director',
        'server', 'bartender', 'host', 'hostess', 'cook', 'line cook',
        'a.m.', 'p.m.', 'morning', 'evening', 'night', 'day', 'weekend'
    ];

    for (const prefix of jobTitlePrefixes) {
        if (namePart.toLowerCase().startsWith(prefix.toLowerCase() + ' ')) {
            // Remove just this prefix
            namePart = namePart.substring(prefix.length).trim();
            log.info(`Removed job title prefix "${prefix}": "${namePart}"`);
            break;
        }
    }

    // Step 10: Check if what's left is just a generic term or a location name
    // If it is, mark it as unknown since it's not a specific company name
    const lowerNamePart = namePart.toLowerCase();

    // Check for generic terms - these are rejected regardless of context
    if (genericTerms.some(term => lowerNamePart === term.toLowerCase())) {
        log.info(`Generic term detected, not a company name: "${namePart}"`);
        return { name: 'Unknown', location: '' };
    }

    // For these terms, only reject if they're standalone (not part of a larger name)
    // This way "Bobby's Restaurant" is valid, but just "Restaurant" is not
    const wordCount = namePart.split(/\s+/).filter(w => w.length > 0).length;
    if (wordCount === 1 && lowerNamePart.length > 2) {
        if (['restaurant', 'hospitality', 'bar', 'cafe', 'bistro', 'tavern',
             'eatery', 'catering', 'culinary', 'bakery', 'dining'].includes(lowerNamePart)) {
            log.info(`Standalone industry term detected, not a company name: "${namePart}"`);
            return { name: 'Unknown', location: '' };
        }
    }

    // Check if it's just a location name
    if (commonLocations.some(loc => lowerNamePart === loc.toLowerCase())) {
        log.info(`Location name detected, not a company name: "${namePart}"`);
        return { name: 'Unknown', location: '' };
    }

    // Check if it STARTS with a location name (may indicate just a location description)
    // But we need to be careful not to filter out legitimate company names that include locations
    // like "Brooklyn Brewery" or "New York Culinary Group"

    // If it's ONLY a location name, it's not a company
    if (commonLocations.some(loc => lowerNamePart === loc.toLowerCase())) {
        log.info(`Is exactly a location name, not a company name: "${namePart}"`);
        return { name: 'Unknown', location: '' };
    }

    // If it starts with a location but also includes these terms, it's likely a valid company name
    const validLocationPrefixTerms = ['brewery', 'culinary', 'dining', 'restaurants', 'kitchen', 'tavern', 'bistro'];
    const containsValidTerm = validLocationPrefixTerms.some(term => lowerNamePart.includes(term.toLowerCase()));

    // Only reject if it starts with a location, doesn't have valid terms, and is relatively short
    if (namePart.length < 20 &&
        !containsValidTerm &&
        commonLocations.some(loc => lowerNamePart.startsWith(loc.toLowerCase() + ' '))) {
        log.info(`Appears to start with location without valid company indicators: "${namePart}"`);
        return { name: 'Unknown', location: '' };
    }

    // Check for very short names or just initials (likely fragments)
    if (namePart.length < 3 || (namePart.length <= 5 && namePart.split(' ').every(part => part.length === 1))) {
        log.info(`Name too short or just initials, likely a fragment: "${namePart}"`);
        return { name: 'Unknown', location: '' };
    }

    // Final return with clean company name
    log.info(`Final parsed company name: "${namePart}"`);
    return {
        name: namePart || 'Unknown',
        location: '' // We don't care about the location for company name handling
    };
}

// Cache loading function removed - contact collection disabled

// Cache functions removed - contact collection disabled

// Email processing functions removed - contact collection disabled

/**
 * Simplified company info function - contact collection disabled, returns basic info only
 */
async function getCompanyInfoWithSource(searchTerm, searchType = 'company', source = 'unknown') {
    // Check if searchTerm is valid based on searchType
    if (!searchTerm || searchTerm === 'Unknown' || searchTerm.startsWith('Excluded:')) {
        log.info(`Skipping search for invalid/excluded ${searchType}: ${searchTerm || 'unknown'}`);
        return { linkedin: 'N/A', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source: `${source}_skipped` };
    }

    // Basic exclusion check (can be enhanced later)
    if (searchType === 'company') {
        const lowerCleanedName = cleanSpecialCharacters(searchTerm).toLowerCase();
        const normalizedName = lowerCleanedName.replace(/\s+/g, '');
        if (EXCLUDED_COMPANIES.has(lowerCleanedName) ||
            Array.from(EXCLUDED_COMPANIES).some(excluded => normalizedName.includes(excluded.replace(/\s+/g, '')))) {
            log.info(`Skipping exactly excluded company: "${searchTerm}"`);
            return { linkedin: 'Excluded', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source: `${source}_excluded` };
        }
        for (const partialTerm of PARTIAL_EXCLUSIONS) {
            const normalizedTerm = partialTerm.replace(/\s+/g, '');
            if (lowerCleanedName.includes(partialTerm) || normalizedName.includes(normalizedTerm)) {
                log.info(`Skipping partially excluded company: "${searchTerm}" (contains "${partialTerm}")`);
                return { linkedin: 'Excluded', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source: `${source}_excluded` };
            }
        }
    }

    // Contact collection disabled - return basic structure with empty emails
    log.info(`Contact collection disabled for ${searchType}: "${searchTerm}" - returning empty contact data`);

    // For domain searches, we can still return the domain
    const resultDomain = searchType === 'domain' ? searchTerm : 'N/A';

    // Return basic structure with empty emails - contact collection disabled
    const finalResult = {
        linkedin: 'N/A',
        domain: resultDomain,
        size: 'N/A',
        emails: [], // No contact collection
        timestamp: now(),
        source: `${source}_contact_disabled`,
        originalCompany: searchTerm
    };

    log.info(`Contact collection disabled for ${searchType} "${searchTerm}" (${source}): LinkedIn=${finalResult.linkedin}, Domain=${finalResult.domain}, Emails=None`);

    return finalResult;
}

// Function to extract potential company names from the address
function extractPotentialCompaniesFromAddress(address) {
    if (!address || typeof address !== 'string' || address === 'N/A') {
        return [];
    }

    // Common address patterns to ignore
    const ignoredWords = new Set([
        'street', 'st', 'avenue', 'ave', 'road', 'rd', 'blvd', 'boulevard', 'drive', 'dr',
        'lane', 'ln', 'court', 'ct', 'place', 'pl', 'way', 'circle', 'cir', 'suite', 'ste',
        'floor', 'fl', 'unit', 'apt', 'apartment', '#'
    ]);

    // Generic terms that should not be considered company names on their own
    const genericAddressTerms = [
        'restaurant group', 'hospitality group', 'restaurant', 'hospitality',
        'group', 'consulting', 'management', 'fine dining'
    ];

    // Check if the address contains numbers that might be street addresses
    const hasStreetNumber = /\b\d+\b/.test(address);

    // Split by common delimiters
    const parts = address.split(/[,|•|\/|-]+/).map(part => part.trim());
    const potentialCompanies = [];

    for (const part of parts) {
        // Skip short parts and parts with just numbers
        if (part.length < 4 || /^\d+$/.test(part)) {
            continue;
        }

        // Skip generic terms that aren't specific company names
        if (genericAddressTerms.some(term => part.toLowerCase() === term)) {
            continue;
        }

        // Skip if part contains too many ignored words
        const words = part.toLowerCase().split(/\s+/);
        const ignoredCount = words.filter(word => ignoredWords.has(word)).length;

        // Skip parts that look like street addresses
        if (hasStreetNumber && (ignoredCount > 0 || /\b\d+\b/.test(part))) {
            continue;
        }

        // Looks like a city+state pattern
        if (/[A-Z]{2}$/.test(part) && part.length <= 12) {
            continue;
        }

        // This part might be a company name
        potentialCompanies.push(part);
    }

    return potentialCompanies;
}

/**
 * Orchestrates fetching company info, prioritizing Google for URL then Hunter for domain.
 */
async function getCompanyInfo(rawCompanyName, rawLocation = '', parentCompanyName = null) {
    const { name: primaryCompanyName } = parseCompanyAndLocation(rawCompanyName);
    const { name: parsedParentCompany } = parentCompanyName ? parseCompanyAndLocation(parentCompanyName) : { name: null };

    let allResults = [];
    const searchTasks = [];

    // --- Define Search Strategies ---
    // 1. Primary Company Name via Google -> Hunter Domain Search
    // Check if primary company is excluded before attempting search
    if (primaryCompanyName && !primaryCompanyName.startsWith('Excluded')) {
        searchTasks.push(async () => {
            log.info(`Starting Google -> Hunter strategy for primary company: "${primaryCompanyName}"`);
            const websiteUrl = await getWebsiteUrlFromGoogle(primaryCompanyName, rawLocation); // rawLocation currently unused by google search
            if (websiteUrl) {
                const domain = getDomainFromUrl(websiteUrl);
                if (domain) {
                    return await getCompanyInfoWithSource(domain, 'domain', 'primary_google_domain');
                }
            }
            log.info(`Google strategy failed for primary company "${primaryCompanyName}", falling back to company name search.`);
            // Fallback: Search Hunter by company name if Google fails
            return await getCompanyInfoWithSource(primaryCompanyName, 'company', 'primary_company_name_fallback');
        });
    } else {
        log.info(`Skipping API searches for excluded/invalid primary company: "${primaryCompanyName}"`);
    }

    // 2. Parent Company Name via Google only (if applicable)
    // Check if parent company is valid and not excluded
    if (parsedParentCompany && parsedParentCompany !== primaryCompanyName && !parsedParentCompany.startsWith('Excluded')) {
        searchTasks.push(async () => {
            log.info(`Starting Google-only strategy for parent company: "${parsedParentCompany}"`);
            const parentWebsiteUrl = await getWebsiteUrlFromGoogle(parsedParentCompany, ''); // Location less relevant for parent
            if (parentWebsiteUrl) {
                const parentDomain = getDomainFromUrl(parentWebsiteUrl);
                if (parentDomain) {
                    return await getCompanyInfoWithSource(parentDomain, 'domain', 'parent_google_domain');
                }
            }
            log.info(`Google strategy failed for parent company "${parsedParentCompany}". No fallback to Hunter API for parent companies.`);
            // No fallback to Hunter API for parent companies to avoid incorrect matches
            return { linkedin: 'N/A', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source: 'parent_company_no_google_result' };
        });
    }

    // --- Execute Search Strategies ---
    // Run strategies sequentially for now to manage API limits and logging clarity
    for (const task of searchTasks) {
        try {
            const result = await task();
            if (result) {
                allResults.push(result);
            }
        } catch (error) {
            log.error(`Error executing search strategy: ${error.message}`);
        }
    }

    // --- Merge Results ---
    log.info(`Merging results from ${allResults.length} search strategies...`);
    const mergedResult = {
        linkedin: '', // Changed to accumulate
        domain: '',   // Changed to accumulate
        size: 'N/A',
        emails: [],
        timestamp: now(),
        source: 'merged',
        sourcesWithEmails: 0
    };
    const addedEmails = new Set();
    const linkedins = new Set();
    const domains = new Set();

    // Sort results: prioritize domain searches, then those with more emails
    allResults.sort((a, b) => {
        const aIsDomain = a.source?.includes('_domain');
        const bIsDomain = b.source?.includes('_domain');
        if (aIsDomain !== bIsDomain) return aIsDomain ? -1 : 1; // Domains first
        return (b.emails?.length || 0) - (a.emails?.length || 0); // Then by email count
    });

    // Process sorted results
    for (const result of allResults) {
        // Collect unique non-error LinkedIn URLs and Domains
        if (result.linkedin && result.linkedin !== 'N/A' && result.linkedin !== 'Excluded' && result.linkedin !== 'Error') {
            result.linkedin.split('; ').forEach(url => linkedins.add(url));
        }
        if (result.domain && result.domain !== 'N/A') {
            // Only add the first domain from each result to avoid mixing company and parent domains
            const firstDomain = result.domain.split('; ')[0];
            domains.add(firstDomain);
        }

        // Get company size from the best available source (first one with valid size)
        if (mergedResult.size === 'N/A' && result.size && result.size !== 'N/A') {
            mergedResult.size = result.size;
        }

        // Add unique emails, attributing source
        if (result.emails && result.emails.length > 0) {
            mergedResult.sourcesWithEmails++;
            for (const email of result.emails) {
                if (email.email) {
                    const emailKey = email.email.toLowerCase();
                    if (!addedEmails.has(emailKey)) {
                        addedEmails.add(emailKey);
                        // Add source information from the specific Hunter result
                        mergedResult.emails.push({
                            ...email,
                            source: result.source || 'unknown_source'
                        });
                    }
                }
            }
        }
    }

    // Finalize accumulated LinkedIn and Domain strings
    mergedResult.linkedin = Array.from(linkedins).join('; ') || 'N/A';
    const finalDomains = Array.from(domains); // Keep as an array first

    // Use only the first domain as the primary domain, not a concatenated string
    mergedResult.domain = finalDomains.length > 0 ? finalDomains[0] : 'N/A';

    // We no longer use the second domain as the parent domain
    // Parent domain will be set explicitly later if available
    mergedResult.parentDomain = null;

    // Store all domains for reference (used for email matching)
    mergedResult.allDomains = finalDomains;

    // Add flag for matching final domain
    if (finalDomains.length > 0) {
        mergedResult.emails.forEach(email => {
            if (email.email) {
                const emailDomain = getDomainFromUrl(email.email);
                if (emailDomain) {
                    // Check if emailDomain exists in the list of final domains found
                    email.matchesFinalDomain = finalDomains.some(fd => fd.toLowerCase() === emailDomain.toLowerCase());
                } else {
                    email.matchesFinalDomain = false; // Couldn't parse email domain
                }
            } else {
                email.matchesFinalDomain = false; // No email address
            }
        });
        log.info(`Added matchesFinalDomain flag to ${mergedResult.emails.length} emails based on final domains: [${finalDomains.join(', ')}]`);
    } else {
         // If no final domain was found, mark all as false
         mergedResult.emails.forEach(email => {
             email.matchesFinalDomain = false;
         });
         log.info(`No final domains found, setting matchesFinalDomain=false for all emails.`);
    }
    // *** END NEW ***

    // Sort final merged emails by job title priority
    mergedResult.emails.sort((a, b) => getTitlePriority(a.title) - getTitlePriority(b.title));

    log.info(`MERGE SUMMARY for "${primaryCompanyName}": Found ${mergedResult.emails.length} unique emails from ${mergedResult.sourcesWithEmails} strategies.`);
    log.info(`Final LinkedIn: ${mergedResult.linkedin}`);
    log.info(`Final Domain: ${mergedResult.domain}`);
    if (mergedResult.parentDomain) {
        log.info(`Parent Domain: ${mergedResult.parentDomain}`);
    }

    return mergedResult;
}

function ensureAbsoluteUrl(url) {
    if (!url) return null;
    return url.startsWith('http') ? url : `${BASE_URL}${url.startsWith('/') ? '' : '/'}${url}`;
}

// Global variables
let sheetsClient = null;
let existingData = new Map();

// --- START: Added Google Sheets Functions ---

// Load existing data from Google Sheet
async function loadExistingData() {
    if (!sheetsClient) {
        log.error('Google Sheets client not initialized before calling loadExistingData');
        throw new Error('Google Sheets client not initialized');
    }
    // Use the globally initialized sheetsClient
    try {
        const response = await sheetsClient.spreadsheets.values.get({
            spreadsheetId: SHEET_ID,
            range: SHEET_NAME, // Use SHEET_NAME defined above
        });
        const rows = response.data.values || [];
        log.info(`Loaded ${rows.length} rows from Google Sheets`);
        // Simple map for quick lookup (e.g., by Job URL or a unique identifier)
        // Modify this based on how you want to check for duplicates
        const dataMap = new Map();
        rows.forEach((row, index) => {
            if (index === 0) return; // Skip header row if present
            const jobUrl = row[9]; // Assuming URL is in the 10th column (index 9)
            if (jobUrl) {
                 // Store the row index or some indicator that the URL exists
                dataMap.set(jobUrl, index + 1);
            }
        });
        log.info(`Created map with ${dataMap.size} existing job URLs.`);
        return dataMap; // Return the map for duplicate checking
    } catch (error) {
        log.error('Failed to load existing data from Google Sheets:', error);
        // Decide if you want to throw or return an empty map/handle differently
        // For now, let's return an empty map to allow the script to continue potentially
         return new Map();
        // throw error; // Or re-throw if loading is critical
    }
}


// Export data to Google Sheet using Append
// Uses the multi-row format with start/end markers per job
async function exportData(data) {
    if (!sheetsClient) {
        log.error('Google Sheets client not initialized');
        throw new Error('Google Sheets client not initialized');
    }

    try {
        // Define headers
        const headers = [
            'Title', 'Company', 'Parent Company', 'Location', 'Salary',
            'Contact Name', 'Contact Title', 'Email Address', 'URL',
            'Job Details', 'LinkedIn', 'Domain', 'Company Size', 'Date Added'
        ];

        // Prepare rows
        const values = [headers]; // Start with headers

        // Process each job
        for (const item of data) {
            if (item.emails && item.emails.length > 0) {
                // Add a row for each contact
                for (const email of item.emails) {
                    const row = [
                item.title || '',
                item.company || '',
                item.parentCompany || 'N/A',
                item.location || '',
                item.salary || '',
                        email.name || 'Unknown',
                        email.title || 'N/A',
                        email.email || '',
                item.url || '',
                        item.jobDetails ? item.jobDetails.substring(0, MAX_CELL_LENGTH) : '',
                item.linkedin || '',
                item.domain || '',
                item.size || '',
                        new Date().toISOString()
                    ];
                    values.push(row);
                }
            } else {
                // Add a single row for jobs with no contacts
                const row = [
                    item.title || '',
                    item.company || '',
                    item.parentCompany || 'N/A',
                    item.location || '',
                    item.salary || '',
                    '(No Contacts Found)',
                        '',
                        '',
                    item.url || '',
                    item.jobDetails ? item.jobDetails.substring(0, MAX_CELL_LENGTH) : '',
                    item.linkedin || '',
                    item.domain || '',
                    item.size || '',
                    new Date().toISOString()
                ];
                values.push(row);
            }
        }

        // Write to sheet starting at A1
        const result = await sheetsClient.spreadsheets.values.update({
            spreadsheetId: SHEET_ID,
            range: 'Sheet1!A1',
            valueInputOption: 'USER_ENTERED',
            resource: { values }
        });

        log.info(`Successfully wrote ${values.length} rows to Google Sheets`);
        return result;
    } catch (error) {
        log.error('Failed to export data to Google Sheets:', error);
        throw error;
    }
}

// --- END: Added Google Sheets Functions ---

async function exportToPostgres(data) {
    log.info(`>>> Entering exportToPostgres with ${data?.length || 0} items.`);

    if (!Array.isArray(data) || data.length === 0) {
        log.warn('exportToPostgres called with invalid or empty data. Exiting.');
        return;
    }

    let client;
    let skippedCount = 0;
    try {
        log.info('Attempting to connect to database pool...');
        client = await pool.connect();
        log.info('Successfully connected client from pool.');

        try {
            log.info('Starting database transaction (BEGIN).');
            await client.query('BEGIN');

            for (const job of data) {
                // Check for essential fields before attempting insert
                if (!job || !job.url || !job.title || !job.company) {
                    log.warn('Skipping job due to missing essential fields (url, title, or company):', job);
                    skippedCount++;
                    continue;
                }

                // First insert/update the job
                const jobQuery = `
                    INSERT INTO culinary_jobs (
                        title, company, parent_company, location, salary,
                        url, job_details, linkedin, domain, parent_url, company_size, date_added
                    ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, NOW())
                    ON CONFLICT (url) DO UPDATE SET
                        title = EXCLUDED.title,
                        company = EXCLUDED.company,
                        parent_company = EXCLUDED.parent_company,
                        location = EXCLUDED.location,
                        salary = EXCLUDED.salary,
                        job_details = EXCLUDED.job_details,
                        linkedin = EXCLUDED.linkedin,
                        domain = EXCLUDED.domain,
                        parent_url = EXCLUDED.parent_url,
                        company_size = EXCLUDED.company_size,
                        last_updated = NOW()
                    RETURNING id`;

                log.info(`DB EXPORT: Preparing to insert/update job: ${job.title} at ${job.company}`);
                log.info(`DB EXPORT: Domain values - Primary: ${job.domain || 'N/A'}, Parent: ${job.parentUrl || 'N/A'}`);

                const jobResult = await client.query(jobQuery, [
                    job.title || '',
                    job.company || '',
                    job.parentCompany || null,
                    job.location || '',
                    job.salary || '',
                    job.url,
                    job.jobDetails || '',
                    job.linkedin || null,
                    job.domain || null,
                    job.parentUrl || null, // Add the parent_url parameter
                    job.size || null,
                ]);

                log.info(`DB EXPORT: Job inserted/updated successfully with ID: ${jobResult.rows[0].id}`);

                const jobId = jobResult.rows[0].id;

                // Now handle contacts if they exist
                if (job.emails && Array.isArray(job.emails) && job.emails.length > 0) {
                    log.info(`Processing ${job.emails.length} contacts for job: ${job.title}`);

                    // First, delete any existing contacts for this job to avoid duplicates
                    await client.query('DELETE FROM culinary_contacts WHERE job_id = $1', [jobId]);

                    // Then insert all contacts
                    for (const contact of job.emails) {
                        if (!contact.email) continue; // Skip if no email

                        const contactQuery = `
                            INSERT INTO culinary_contacts (
                                job_id, name, title, email, date_added
                            ) VALUES ($1, $2, $3, $4, NOW())
                            ON CONFLICT (email, job_id) DO UPDATE SET
                                name = EXCLUDED.name,
                                title = EXCLUDED.title,
                                last_updated = NOW()`;

                        await client.query(contactQuery, [
                            jobId,
                            contact.name || 'Unknown',
                            contact.title || 'N/A',
                            contact.email
                        ]);
                    }
                }
            }

            if (skippedCount === data.length) {
                log.warn(`All ${skippedCount} jobs in the batch were skipped due to missing fields. Committing empty transaction.`);
            } else {
                log.info(`Processed ${data.length - skippedCount} jobs in the batch. Attempting COMMIT.`);
            }

            await client.query('COMMIT');
            log.info(`Successfully COMMITTED transaction for ${data.length - skippedCount} jobs.`);

        } catch (err) {
            log.error('DATABASE TRANSACTION ERROR (inside try/catch):', err);
            log.error('Failed job data (first item in batch):', data.length > 0 ? JSON.stringify(data[0], null, 2) : 'N/A');
            if (client) {
                log.info('Attempting ROLLBACK...');
                await client.query('ROLLBACK');
                log.info('ROLLBACK successful.');
            } else {
                log.warn('Client was not defined, cannot ROLLBACK.');
            }
            throw err;
        } finally {
            if (client) {
                log.info('Releasing database client...');
                client.release();
                log.info('Client released.');
            } else {
                log.warn('Client was not defined, cannot release.');
            }
        }
    } catch (error) {
        log.error('DATABASE EXPORT PROCESS ERROR (outer catch):', error);
        log.error('Failed job data (first item in batch, outer catch):', data.length > 0 ? JSON.stringify(data[0], null, 2) : 'N/A');
        throw error;
    }
    log.info(`<<< Exiting exportToPostgres after processing ${data?.length || 0} items.`);
}

// Update the batch export handler
async function handleBatchExport() {
    if (exportBatch.length >= EXPORT_BATCH_SIZE) {
        console.log(`Batch size ${exportBatch.length} reached, exporting...`); // Use console.log
        try {
            await exportToPostgres(exportBatch);
            exportBatch = []; // Clear the batch after successful export
            console.log('Batch export completed successfully'); // Use console.log
        } catch (error) {
            console.error('Failed to export batch:', error); // Use console.error
            // Keep the batch for retry on next attempt
        }
    }
}

async function createTables() {
    const client = await pool.connect();
    try {
        // Create an enum type for job status if needed
        // await client.query(`
        //     DO $$ BEGIN
        //         CREATE TYPE job_status AS ENUM ('active', 'filled', 'expired');
        //     EXCEPTION
        //         WHEN duplicate_object THEN null;
        //     END $$;
        // `);

        // Create the jobs table with improved structure
        await client.query(`
            CREATE TABLE IF NOT EXISTS culinary_jobs (
                id SERIAL PRIMARY KEY,
                title VARCHAR(255) NOT NULL,
                company VARCHAR(255) NOT NULL,
                parent_company VARCHAR(255),
                location VARCHAR(255),
                salary VARCHAR(255),
                contact_name VARCHAR(255),
                contact_title VARCHAR(255),
                email VARCHAR(255),
                url TEXT UNIQUE NOT NULL,
                job_details TEXT,
                linkedin VARCHAR(255),
                domain VARCHAR(255),
                parent_url VARCHAR(255),
                company_size VARCHAR(50),
                date_added TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
                last_updated TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,

                -- Add indexes for common queries
                CONSTRAINT unique_job_url UNIQUE (url),
                CONSTRAINT unique_job_email UNIQUE (email, company)
            );

            -- Add indexes for performance
            CREATE INDEX IF NOT EXISTS idx_company_name ON culinary_jobs(company);
            CREATE INDEX IF NOT EXISTS idx_job_title ON culinary_jobs(title);
            CREATE INDEX IF NOT EXISTS idx_email ON culinary_jobs(email);
            CREATE INDEX IF NOT EXISTS idx_date_added ON culinary_jobs(date_added);
        `);

        // Create the contacts table linked to the jobs table
        await client.query(`
            CREATE TABLE IF NOT EXISTS culinary_contacts (
                id SERIAL PRIMARY KEY,
                job_id INTEGER NOT NULL REFERENCES culinary_jobs(id) ON DELETE CASCADE,
                name VARCHAR(255),
                title VARCHAR(255),
                email VARCHAR(255) NOT NULL,
                date_added TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
                last_updated TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,

                -- Constraint to prevent duplicate emails for the same job
                CONSTRAINT unique_contact_for_job UNIQUE (job_id, email)
            );

            -- Add index for faster lookups by job_id
            CREATE INDEX IF NOT EXISTS idx_contact_job_id ON culinary_contacts(job_id);
            -- Add index for faster lookups by email (optional, depends on query patterns)
            CREATE INDEX IF NOT EXISTS idx_contact_email ON culinary_contacts(email);
        `);

        log.info('Database tables and indexes created successfully');
    } catch (error) {
        log.error('Error creating database tables:', error);
        throw error;
    } finally {
        client.release();
    }
}

// Use Actor.main() for the main execution block
Actor.main(async () => {
    const startTime = Date.now(); // Track start time
    let newlyAddedJobs = [];
    let skippedDuplicateJobs = [];
    let skippedExcludedJobs = [];

    // Get input parameters
    const input = await Actor.getInput() || {};

    // Set API keys from input or environment variables
    if (input.googlePlacesApiKey) {
        process.env.GOOGLE_PLACES_API_KEY = input.googlePlacesApiKey;
        log.info('Using Google Places API Key from input');
    }

    if (input.resendApiKey) {
        process.env.RESEND_API_KEY = input.resendApiKey;
        log.info('Using Resend API Key from input');
    }

    // Create new variables for input values instead of modifying constants
    const inputTestMode = input.testMode !== undefined ? input.testMode : TEST_MODE;
    const inputTestJobLimit = input.testJobLimit !== undefined ? input.testJobLimit : TEST_JOB_LIMIT;
    const inputExportData = input.exportData !== undefined ? input.exportData : EXPORT_DATA;

    log.info(`Using test mode: ${inputTestMode}`);
    log.info(`Using test job limit: ${inputTestJobLimit}`);
    log.info(`Using export data: ${inputExportData}`);

    // Cache functionality removed - contact collection disabled
    if (input.clearCache === true) {
        log.info('Cache functionality disabled - ignoring clearCache setting');
    }

    // Initialize parentCompany variable
    let parentCompany = null;

    // Add parent company domain lookup if parent company exists
    let parentDomain = null;
    if (parentCompany) {
        log.info(`PARENT LOOKUP: Starting domain lookup for parent company "${parentCompany}"`);

        // Try to get parent company domain via Google
        log.info(`PARENT LOOKUP: Attempting Google Places search for "${parentCompany}"`);
        const parentWebsiteUrl = await getWebsiteUrlFromGoogle(parentCompany, '');

        if (parentWebsiteUrl) {
            parentDomain = getDomainFromUrl(parentWebsiteUrl);
            log.info(`PARENT LOOKUP: SUCCESS - Found parent company domain via Google: ${parentDomain}`);
        } else {
            log.info(`PARENT LOOKUP: Google search failed for "${parentCompany}". Not using Hunter API for parent companies.`);
            // No fallback to Hunter API for parent companies to avoid incorrect matches
        }

        // Final status log
        if (parentDomain) {
            log.info(`PARENT LOOKUP: FINAL RESULT - Will use domain "${parentDomain}" for parent company "${parentCompany}"`);
        } else {
            log.info(`PARENT LOOKUP: FINAL RESULT - No domain found for parent company "${parentCompany}"`);
        }
    }
    const reportedJobUrls = new Set(); // Track URLs added to email report to prevent duplicates
    let state = null; // Initialize state here to access in finally block

    try {
        // Test database connection first
        if (!await testDatabaseConnection()) { // Ensure testDatabaseConnection is defined below
            throw new Error('Failed to connect to database');
        }

        // Create tables if they don't exist
        try {
            await createTables(); // Ensure createTables is defined below
            log.info('Database tables initialized successfully');
        } catch (dbError) {
            log.error('Error initializing database tables:', dbError);
            throw dbError;
        }

        // Load existing job URLs from the database BEFORE starting the crawler
        const existingUrlsFromDB = await loadExistingJobUrlsFromDB();

        // Initialize state store and request queue
        const stateStore = await KeyValueStore.open();
        // state = await stateStore.getValue('SCRAPE_STATE') || { processedCount: 0 }; // Moved initialization up
        state = await stateStore.getValue('SCRAPE_STATE') || { processedCount: 0, attemptedCount: 0 }; // Added attemptedCount
        const requestQueue = await RequestQueue.open();

        // Add initial search URL
        await requestQueue.addRequest({
            url: 'https://culinaryagents.com/search/jobs?search%5Bcompensation%5D%5B%5D=salary',
            userData: { page: 1 }
        });

        // Configure crawler (Changed back to CheerioCrawler)
        const crawler = new CheerioCrawler({
            requestQueue,
            maxRequestRetries: 3,
            // Add concurrency/rate limits from old code
            maxConcurrency: 1,
            minConcurrency: 1,
            requestHandlerTimeoutSecs: 120,
            maxRequestsPerMinute: inputTestMode ? 2 : 6,
            // REMOVED launchContext and preNavigationHooks

            // Replace requestHandler with logic from the old snippet
            async requestHandler({ $, request, log }) { // Ensure enqueueLinks is available if needed, or remove if not used by snippet
                log.info(`Processing page ${request.url}`);

                // --- START: Logic from provided snippet ---
                const jobCards = $('.ca-single-job-card');
                log.info(`Found ${jobCards.length} jobs on page ${request.url}`);

                // Assume stateStore is initialized outside
                const stateStore = await KeyValueStore.open();
                // Ensure state is loaded within the handler to get latest values, OR rely on the outer scope state variable.
                // Reloading state here might overwrite increments from concurrent handlers if concurrency > 1.
                // Sticking with outer scope `state` variable for now as concurrency is 1.
                // state = await stateStore.getValue('SCRAPE_STATE') || { processedCount: 0, attemptedCount: 0 }; // Reload state

                // Assume existingDataset is initialized outside
                const existingDataset = await Dataset.open('culinary-jobs');

                // *** REMOVED PLACEHOLDER ***
                // Assume existingUrls Set is initialized outside and populated if needed
                // const existingUrls = new Set(); // Placeholder - this needs proper initialization

                // Assume processedJobsList array is initialized outside for batching
                // let processedJobsList = []; // Placeholder - this needs proper initialization

                if (request.userData?.page === 1 || !request.userData?.page) {
                    const totalJobsText = $('.jobs-count-total').text().trim();
                    const totalJobsMatch = totalJobsText.match(/About ([0-9,]+) jobs/);
                    if (totalJobsMatch && totalJobsMatch[1]) {
                        const totalJobs = parseInt(totalJobsMatch[1].replace(/,/g, ''));
                        log.info(`Found total jobs count: ${totalJobs}`);
                        await stateStore.setValue('TOTAL_JOBS', totalJobs);
                    }
                }

                const listings = [];
                const cardsToProcess = inputTestMode ?
                    Math.min(inputTestJobLimit - (state.processedCount || 0), jobCards.length) :
                    jobCards.length;

                for (let i = 0; i < cardsToProcess; i++) {
                    const el = jobCards[i];
                    const jobUrl = ensureAbsoluteUrl($(el).attr('href')); // ensureAbsoluteUrl must be defined

                    // *** USE THE SET LOADED FROM DB ***
                    if (!jobUrl || existingUrlsFromDB.has(jobUrl)) {
                        if (jobUrl) {
                            log.info(`Skipping existing job: ${jobUrl}`);
                            // Track skipped duplicate
                            skippedDuplicateJobs.push({
                                url: jobUrl,
                                title: $(el).find('.job-title strong').text().trim() || 'N/A',
                                rawCompany: $(el).find('.text-body.text-ellipsis:not(.job-employment)').text().trim() || 'N/A'
                            });
                        }
                        continue;
                    }
                    const title = $(el).find('.job-title strong').text().trim() || 'Unknown';
                    const rawCompany = $(el).find('.text-body.text-ellipsis:not(.job-employment)').text().trim() || 'Unknown';
                    const { name: company } = parseCompanyAndLocation(rawCompany); // parseCompanyAndLocation must be defined

                    // Improved location extraction with better spacing handling
                    let fullAddress = '';
                    const locationElement = $(el).find('.text-muted.text-ellipsis');
                    if (locationElement.length > 0) {
                        // Get text content and handle potential spacing issues
                        fullAddress = locationElement.text().trim();
                        // Clean the location text to fix missing spaces
                        fullAddress = cleanLocationText(fullAddress);
                    }
                    if (!fullAddress) fullAddress = 'N/A';

                    // Skip excluded companies entirely
                    if (company.startsWith('Excluded')) {
                        log.info(`Skipping excluded company job: ${title} at ${rawCompany} (URL: ${jobUrl})`);
                        // Track skipped exclusion
                        skippedExcludedJobs.push({ url: jobUrl, title, rawCompany, reason: company });
                        continue; // Go to the next job card, don't add this one to listings
                    }

                    listings.push({
                        url: jobUrl,
                        title,
                        company,
                        location: fullAddress,
                        searchLocation: cleanCompanyName(fullAddress), // cleanCompanyName must be defined
                        salary: $(el).find('.job-employment').text().trim() || 'N/A'
                    });
                }

                if (listings.length > 0) {
                    log.info(`Processing batch of ${listings.length} new listings`);
                    const jobDetailsArray = [];
                    for (const listing of listings) {
                        // Increment attemptedCount for every job that passed initial filters
                        state.attemptedCount = (state.attemptedCount || 0) + 1;
                        log.debug(`Attempting job ${state.attemptedCount}: ${listing.url}`); // Add debug log

                        try {
                            await delay(inputTestMode ? 1000 : 2000); // delay must be defined
                            const response = await fetch(listing.url, { method: 'GET' });
                            const body = await response.text();
                            if (!response.ok) {
                                log.info(`Failed to fetch job details for ${listing.url}: status ${response.status}`);
                                continue;
                            }
                            const $detail = cheerio.load(body);
                            const jobDetailsText = $detail('#job-details .text-muted div').text().trim() || 'N/A';

                            let parentCompany = null;
                            const partOfElement = $detail('p:contains("Part of")');
                            if (partOfElement.length > 0) {
                                const partOfLink = partOfElement.find('a.text-muted');
                                if (partOfLink.length > 0) {
                                    parentCompany = partOfLink.text().trim();
                                }
                            }

                            let leadership = [];
                            const leadershipSection = $detail('.leadership-section');
                            if (leadershipSection.length > 0) {
                                leadershipSection.find('a.text-body').each((_, leaderEl) => {
                                    const leader = $detail(leaderEl);
                                    const name = leader.find('.font-weight-bold').text().trim();
                                    const title = leader.find('p').text().trim() || 'N/A';
                                    if (name) leadership.push({ name, title });
                                });
                            }

                            // ALWAYS call the main orchestrator function
                            log.info(`Getting contact info for "${listing.company}" (Parent: ${parentCompany || 'N/A'})`);

                            // Get parent domain if parent company exists
                            let parentDomain = null;
                            if (parentCompany) {
                                log.info(`Looking up parent domain for "${parentCompany}"`);
                                // Try to get parent company domain via Google only
                                const parentWebsiteUrl = await getWebsiteUrlFromGoogle(parentCompany, '');
                                if (parentWebsiteUrl) {
                                    parentDomain = getDomainFromUrl(parentWebsiteUrl);
                                    log.info(`Found parent domain via Google: ${parentDomain}`);
                                } else {
                                    log.info(`Google search failed for parent company "${parentCompany}". Not using Hunter API for parent companies.`);
                                    // No fallback to Hunter API for parent companies to avoid incorrect matches
                                }
                            }

                            const contactInfo = await getCompanyInfo(
                                listing.company,     // The primary company name from the listing
                                listing.location,    // The raw location string from the listing
                                parentCompany        // The detected parent company name (or null)
                            );

                            // Add parent domain to contact info if found
                            if (parentDomain) {
                                contactInfo.parentDomain = parentDomain;
                                log.info(`Setting parent domain for ${listing.company}: ${parentDomain}`);
                            }

                            const emailsText = contactInfo.emails.length > 0
                                ? contactInfo.emails.map(e => `${e.name || 'Unknown'}, ${e.title || 'N/A'}, ${e.email || 'N/A'}`).join('; ')
                                : 'No emails found';

                            log.info(`Found ${contactInfo.emails.length} emails for "${listing.company}": ${emailsText}`);

                            let emailsCopy = [];
                            if (contactInfo.emails && contactInfo.emails.length > 0) {
                                const emailsJSON = JSON.stringify(contactInfo.emails);
                                emailsCopy = JSON.parse(emailsJSON);
                                emailsCopy = emailsCopy.slice(0, 20); // Changed from 3 to 20 to get up to 20 best contacts

                                emailsCopy = emailsCopy.map((email, idx) => {
                                    const contactCompany = email._originalCompany || 'unknown';
                                    return {
                                        ...email,
                                        _jobId: `${listing.company.replace(/\s+/g, '-')}-${Date.now()}-${idx}`,
                                        _jobTitle: listing.title,
                                        _company: listing.company,
                                        _timestamp: now(),
                                        _index: idx,
                                        _originalCompany: contactCompany,
                                        _originalDomain: email._originalDomain || 'unknown',
                                        _matchesJobCompany: contactCompany.toLowerCase() === listing.company.toLowerCase(),
                                        _processingTime: Date.now()
                                    };
                                });
                            }

                            const jobDetail = {
                                title: String(listing.title || ''),
                                company: String(listing.company || ''),
                                location: String(listing.location || ''),
                                salary: String(listing.salary || ''),
                                url: String(listing.url || ''),
                                searchLocation: String(listing.searchLocation || ''),
                                jobDetails: truncateText(jobDetailsText), // truncateText must be defined
                                leadership: leadership.length > 0 ? [...leadership] : 'N/A',
                                parentCompany: parentCompany || 'N/A',
                                linkedin: contactInfo.linkedin || 'N/A',
                                contactLink: contactInfo.linkedin || 'N/A',
                                emails: emailsCopy,
                                emailsText,
                                domain: contactInfo.domain || 'N/A',
                                parentUrl: contactInfo.parentDomain || null, // Add parent domain URL
                                size: contactInfo.size || 'N/A',
                                dataSource: contactInfo.source || 'unknown',
                                dataDate: now(),
                                dateAdded: now(),
                                _processId: Date.now()
                            };

                            const verifiedDetail = JSON.parse(JSON.stringify(jobDetail));
                            jobDetailsArray.push(verifiedDetail);
                            // Track newly added job details for reporting - ENSURE UNIQUE
                            if (!reportedJobUrls.has(verifiedDetail.url)) {
                                log.info(`Adding to email report (URL: ${verifiedDetail.url})`); // Added log
                                newlyAddedJobs.push({
                                    title: verifiedDetail.title,
                                    company: verifiedDetail.company,
                                    parentCompany: verifiedDetail.parentCompany,
                                    location: verifiedDetail.location
                                });
                                reportedJobUrls.add(verifiedDetail.url); // Add URL to set
                            } else {
                                log.info(`Skipping email report for already reported URL: ${verifiedDetail.url}`); // Added log
                            }
                            log.info(`Processed job: ${listing.title} at ${listing.company} with ${verifiedDetail.emails.length} contacts`);
                            // Correctly increment processedCount here, attemptedCount is incremented before fetch
                            state.processedCount = (state.processedCount || 0) + 1;
                        } catch (error) {
                            log.error(`Error fetching details for ${listing.url}: ${error.message}`);
                            // Note: state.attemptedCount was already incremented, state.processedCount was not.
                        }
                    }

                    if (jobDetailsArray.length > 0) {
                        try {
                            await existingDataset.pushData(jobDetailsArray);
                            const jobDetailsCopy = JSON.parse(JSON.stringify(jobDetailsArray));

                            // Validation for duplicate emails within the same job
                            jobDetailsCopy.forEach(job => {
                                if (job.emails && job.emails.length > 0) {
                                    const jobEmailMap = new Map();
                                    job.emails = job.emails.filter(email => {
                                        const emailKey = email.email.toLowerCase();
                                        if (jobEmailMap.has(emailKey)) return false;
                                        jobEmailMap.set(emailKey, true);
                                        return true;
                                    });
                                }
                            });

                            exportBatch.push(...jobDetailsCopy); // Use global exportBatch
                            log.info(`Current export batch size: ${exportBatch.length}`);
                            await stateStore.setValue('SCRAPE_STATE', state);

                            if (exportBatch.length >= EXPORT_BATCH_SIZE) {
                                log.info(`EXPORT TRIGGERED: Batch size ${exportBatch.length}`);
                                // Create a copy of the batch for logging purposes
                                log.info(`Exporting ${exportBatch.length} jobs...`);
                                await handleBatchExport(); // This function now uses the global exportBatch
                                log.info(`Cleared export batch after successful/attempted export.`);
                                // Note: handleBatchExport should clear the global exportBatch on success
                            }
                        } catch (error) {
                            log.error(`Failed to process batch: ${error.message}`);
                        }
                    }
                }

                // --- Test Mode Check ---
                // Add this block BEFORE the main pagination logic
                if (inputTestMode && (state.processedCount || 0) >= inputTestJobLimit) {
                    log.info(`Test mode: Reached limit of ${state.processedCount || 0}/${inputTestJobLimit} processed jobs. Stopping crawler.`);
                    // Save state one last time before stopping
                    await stateStore.setValue('SCRAPE_STATE', state);
                    return; // Exit the handler to prevent queueing next page
                }

                // --- Calculate current accounted jobs ---
                const accountedJobs = (skippedDuplicateJobs.length + skippedExcludedJobs.length + (state.attemptedCount || 0));
                const totalJobsTarget = await stateStore.getValue('TOTAL_JOBS') || 2000; // Use a default if not found

                log.info(`Jobs accounted for: ${accountedJobs} (Skipped D: ${skippedDuplicateJobs.length}, Skipped E: ${skippedExcludedJobs.length}, Attempted: ${state.attemptedCount || 0}) / Target: ${totalJobsTarget}`);

                // Check if we should stop queueing
                const shouldContinue = jobCards.length > 0 && accountedJobs < totalJobsTarget;

                if (shouldContinue) {
                    const nextPage = request.userData?.page || 1;
                    const jobsPerPage = 20; // Culinary Agents shows 20 jobs per page
                    const nextPageUrl = `https://culinaryagents.com/search/jobs?search%5Bcompensation%5D%5B%5D=salary&offset=${nextPage * jobsPerPage}`; // Use jobsPerPage here
                    log.info(`Continuing crawl: Accounted for ${accountedJobs}/${totalJobsTarget}. Queueing next page (${nextPage + 1}): ${nextPageUrl}`);
                    await delay(inputTestMode ? 5000 : 30000); // Consider reducing delay if only skipping
                    await requestQueue.addRequest({ url: nextPageUrl, userData: { page: nextPage + 1 } });
                } else {
                    if (jobCards.length === 0) {
                         log.info(`Stopping crawl: Current page had 0 job cards.`);
                    } else {
                        log.info(`Stopping crawl: Accounted for ${accountedJobs}/${totalJobsTarget} jobs.`);
                    }
                    // Save state one last time potentially
                    await stateStore.setValue('SCRAPE_STATE', state);
                }
                // --- END: Logic from provided snippet ---
            },

            failedRequestHandler({ request, error, log }) {
                log.error(`Request ${request.url} failed: ${error.message}`);
            }
        });

        // Run crawler with timeout logic
        log.info('Starting Cheerio crawler...');
        const MAX_RUNTIME_MS = 4 * 60 * 60 * 1000; // 4 hours
        const startTime = Date.now();
        const timeoutPromise = new Promise((_, reject) => { // Reject on timeout
            setTimeout(() => {
                reject(new Error(`Maximum runtime of ${MAX_RUNTIME_MS / 1000 / 60} minutes reached.`));
            }, MAX_RUNTIME_MS);
        });

        try {
             await Promise.race([
                 crawler.run(),
                 timeoutPromise
             ]);
             const runtimeMs = Date.now() - startTime;
             log.info(`Crawler completed naturally after ${runtimeMs / 1000 / 60} minutes.`);
        } catch (timeoutError) {
            log.error(timeoutError.message);
            log.info(`Crawler stopped due to reaching maximum runtime.`);
            // Optionally drop queue if timeout occurs
            // await requestQueue.drop();
        }

        // Cache functionality removed - contact collection disabled

        // Final export if any remaining jobs
        if (inputExportData && exportBatch.length > 0) { // Use global exportBatch
            log.info(`Exporting final batch of ${exportBatch.length} results...`);
            // Create a copy of the batch for logging purposes
            log.info(`Exporting ${exportBatch.length} jobs...`);
            await handleBatchExport(); // Should use and clear global exportBatch
        }
        log.info(`Scraping completed! Total jobs processed: ${state ? state.processedCount : 'N/A'}`);
        // Optionally log dataset size
        // const finalData = await existingDataset.getData();
        // log.info(`Final dataset contents: ${finalData.items.length} items`);

    } catch (err) {
        log.error(`Fatal error: ${err.message}`);
        if (err.stack) log.error(err.stack);
    } finally {
        // Ensure final batch export happens even on error/timeout
        if (inputExportData && exportBatch.length > 0) { // Use global exportBatch
            console.warn(`Error or timeout occurred. Exporting final batch of ${exportBatch.length} results...`); // Use console.warn
            try {
                await handleBatchExport();
            } catch (exportError) {
                log.error("Error during final batch export in finally block:", exportError);
            }
        }

        // Send completion email
        const endTime = Date.now();
        const durationMs = endTime - startTime;
        await sendCompletionEmail({
            startTime,
            endTime,
            durationMs,
            processedCount: state ? state.processedCount : 0,
            newlyAddedJobs,
            skippedDuplicateJobs,
            skippedExcludedJobs
        });

        await pool.end();
        log.info("Database pool closed.");
    }
});

// *** ADDED FUNCTION: Send Completion Email ***
async function sendCompletionEmail(stats) {
    console.log("Preparing completion email..."); // Use console.log
    const apiKey = process.env.RESEND_API_KEY;

    if (!apiKey) {
        console.warn("RESEND_API_KEY environment variable not found. Skipping email notification."); // Use console.warn
        return;
    }

    const resend = new Resend(apiKey);

    // --- Fetch Random Quote ---
    let quoteHtml = '';
    try {
        console.log("Fetching random quote..."); // Use console.log
        const quoteResponse = await fetch('https://api.realinspire.live/v1/quotes/random');
        if (quoteResponse.ok) {
            const quoteData = await quoteResponse.json();
            if (Array.isArray(quoteData) && quoteData.length > 0) {
                const quote = quoteData[0];
                if (quote.content && quote.author) {
                    quoteHtml = `<p style="font-style: italic; margin-top: 20px; padding-top: 10px; border-top: 1px dashed #ccc; color: #000000;">"${quote.content}" - ${quote.author}</p>`;
                    console.log(`Quote fetched: "${quote.content}"`); // Use console.log
                }
            }
        } else {
            console.warn(`Failed to fetch quote: ${quoteResponse.status}`); // Use console.warn
        }
    } catch (quoteError) {
        console.error("Error fetching random quote:", quoteError); // Use console.error
    }
    // --- End Fetch Random Quote ---

    // Format Date/Time in PST
    const completionTimePST = new Date(stats.endTime).toLocaleString("en-US", {
        timeZone: "America/Los_Angeles",
        year: 'numeric', month: 'long', day: 'numeric',
        hour: 'numeric', minute: '2-digit', second: '2-digit', hour12: true
    });
    const todayDate = new Date().toLocaleDateString("en-US", {
        timeZone: "America/Los_Angeles",
        year: 'numeric', month: 'long', day: 'numeric'
    });

    // Format Lists
    // Updated to accept inline style string
    const formatJobList = (jobList, includeParent = false, itemStyle = "") => { // Corrected default parameter syntax
        if (!jobList || jobList.length === 0) return `<li style="${itemStyle}">None</li>`;
        return jobList.map(job =>
            `<li style="${itemStyle}">${job.title || 'N/A'} at ${job.company || job.rawCompany || 'N/A'} ${includeParent && job.parentCompany && job.parentCompany !== 'N/A' ? `(Parent: ${job.parentCompany})` : ''} - ${job.location || 'N/A'}</li>`
        ).join("");
    };

    const newJobStyle = 'font-size: 12pt; color: #000000; text-align: left;';
    const excludedJobStyle = 'font-size: 12pt; color: #000000; text-align: left;';

    const newlyAddedListHtml = formatJobList(stats.newlyAddedJobs, true, newJobStyle);

    // De-duplicate skipped excluded jobs by URL before formatting
    const uniqueSkippedExcludedUrls = new Set();
    const uniqueSkippedExcludedJobs = stats.skippedExcludedJobs.filter(job => {
        if (!job || !job.url) return false; // Skip if job or URL is missing
        const lowerUrl = job.url.toLowerCase();
        if (uniqueSkippedExcludedUrls.has(lowerUrl)) {
            return false;
        } else {
            uniqueSkippedExcludedUrls.add(lowerUrl);
            return true;
        }
    });

    const skippedExcludedListHtml = formatJobList(uniqueSkippedExcludedJobs.map(j => ({...j, company: j.rawCompany})), false, excludedJobStyle);

    // Note: skippedDuplicateJobs only has rawCompany, so we format it slightly differently if needed
    // const skippedDuplicateListHtml = formatJobList(stats.skippedDuplicateJobs, false);

    const subject = `BizDev Results for ${todayDate}`;
    const htmlBody = `
        <p style="font-weight: bold; font-size: 24pt; color: #000000; text-align: center;">Your Culinary Agent scraper completed at ${completionTimePST}</p>
        <p style="color: #000000;">Duration: ${Math.round(stats.durationMs / 60000)} minutes (${Math.round(stats.durationMs / 1000)} seconds)</p>

        <h2>Summary</h2>
        <ul style="color: #000000;">
            <li><b>${stats.processedCount || 0}</b> listings were successfully processed.</li>
            <li><b>${stats.newlyAddedJobs.length}</b> listings added to this email report (unique URL for this run).</li>
            <li><b>${stats.skippedDuplicateJobs.length}</b> listings were skipped (already in DB).</li>
            <li><b>${uniqueSkippedExcludedJobs.length}</b> unique listings were skipped (excluded company).</li>
        </ul>

        <h2>New Listings Processed:</h2>
        <ul style="list-style-type: disc; padding-left: 20px; color: #000000;">
            ${newlyAddedListHtml}
        </ul>

        <hr>

        <h2>Excluded Listings:</h2>
        <p style="font-size: 10pt; color: #000000;">Current Exclusion List (Exact Match): Alliance Personnel, August Point Advisors, Bon Appetit, Capital Restaurant Associates, Chartwells, Compass, CORE Recruitment, EHS Recruiting, Empowered Hospitality, Eurest, Goodwin Recruiting, HMG Plus - New York, LSG Sky Chefs, Major Food Group, Measured HR, One Haus, Patrice & Associates, Persone NYC, Playbook Advisors, Restaurant Associates, Source One Hospitality, STARR, Ten Five Hospitality, The Goodkind Group, Tuttle Hospitality, Willow Tree Recruiting, washington, washington dc, washington d.c., washington d c | (Partial Match): whole foods</p>
        <ul style="list-style-type: disc; padding-left: 20px; color: #000000;">
            ${skippedExcludedListHtml}
        </ul>

        ${quoteHtml}

        <p style="color: #000000;">You can review new listings at <a href="https://madisonbizdev-production.up.railway.app/" style="color: #0000FF;">https://madisonbizdev-production.up.railway.app/</a></p>
    `;

    // *** START CHANGE: Send separate emails ***
    const recipients = ['aj@chefsheet.com', 'martha@madison-collective.com'];
    console.log(`Attempting to send completion emails to: ${recipients.join(', ')}`);

    for (const recipient of recipients) {
        try {
            console.log(`Sending email to ${recipient}...`); // Use console.log
            const { data, error } = await resend.emails.send({
                from: 'Culinary Scraper <onboarding@resend.dev>', // Sender name is good practice
                to: [recipient], // Send to one recipient at a time in an array
                subject: subject,
                html: htmlBody,
            });

            if (error) {
                // Log specific error for this recipient
                console.error(`Failed to send completion email to ${recipient}:`, error); // Use console.error
            } else {
                // Log specific success for this recipient
                console.log(`Completion email sent successfully to ${recipient}:`, data); // Use console.log
            }
        } catch (emailError) {
            // Catch errors during the send process for this recipient
            console.error(`Error during email sending process for ${recipient}:`, emailError); // Use console.error
        }
    }
    // *** END CHANGE ***
}

// Your existing helper functions remain the same...

// Helper function to test database connection
async function testDatabaseConnection() {
    try {
        const client = await pool.connect();
        try {
            const result = await client.query('SELECT NOW()');
            log.info('Successfully connected to database:', result.rows[0].now);
            return true;
        } finally {
            client.release();
        }
    } catch (error) {
        log.error('Failed to connect to database:', error);
        return false;
    }
}

// *** ADDED FUNCTION ***
// Helper function to load existing job URLs from the database
async function loadExistingJobUrlsFromDB() {
    log.info('Loading existing job URLs from database...');
    const existingUrls = new Set();
    let client;
    try {
        client = await pool.connect();
        const result = await client.query('SELECT url FROM culinary_jobs');
        if (result.rows && result.rows.length > 0) {
            result.rows.forEach(row => {
                if (row.url) {
                    existingUrls.add(row.url);
                }
            });
        }
        log.info(`Loaded ${existingUrls.size} existing job URLs from the database.`);
        return existingUrls;
    } catch (error) {
        log.error('Failed to load existing job URLs from database:', error);
        // Return an empty set to allow the crawler to proceed, though it might process duplicates
        return existingUrls;
    } finally {
        if (client) {
            client.release();
        }
    }
}

// *** NEW HELPER FUNCTIONS START ***

/**
 * Extracts the base domain name from a URL.
 * e.g., "https://www.example.com/path?query=1" -> "example.com"
 * Handles common variations.
 */
function getDomainFromUrl(url) {
    if (!url) return null;
    try {
        const parsedUrl = new URL(url.startsWith('http') ? url : `http://${url}`);
        // Use hostname, remove potential 'www.' prefix
        let domain = parsedUrl.hostname;
        if (domain.startsWith('www.')) {
            domain = domain.substring(4);
        }
        return domain;
    } catch (e) {
        console.warn(`Failed to parse URL for domain extraction: ${url}`, e); // Use console
        // Fallback for simple cases if URL constructor fails
        let domain = url.replace(/^https?:\/\//, ''); // Remove http(s)://
        domain = domain.replace(/^www\./, '');       // Remove www.
        domain = domain.split('/')[0];              // Remove path
        domain = domain.split('?')[0];              // Remove query string
        domain = domain.split(':')[0];              // Remove port
        // Basic check if it looks like a domain
        if (domain.includes('.')) {
             return domain;
        }
        return null;
    }
}

// Import the SearchAPI function
import getWebsiteUrlFromSearchAPI from './search_api.js';

/**
 * Uses SearchAPI.io to find the website URL for a business name.
 * This function replaces the previous Google Places API implementation.
 */
async function getWebsiteUrlFromGoogle(companyName, _location) {
    // _location parameter is kept for backward compatibility but not used
    // For backward compatibility, we keep the same function name
    // but now it uses SearchAPI.io instead of Google Places API
    console.info(`Using SearchAPI instead of Google Places for "${companyName}"`);
    return await getWebsiteUrlFromSearchAPI(companyName);

    // The old Google Places API code has been removed
    // If you need to revert, check version control history
}

// *** NEW HELPER FUNCTIONS END ***
