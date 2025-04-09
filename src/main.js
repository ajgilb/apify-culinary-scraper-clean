import { CheerioCrawler, KeyValueStore, RequestQueue, log, Dataset } from 'crawlee';
import cheerio from 'cheerio';
import fetch from 'node-fetch';
import { Actor } from 'apify';
import pkg from 'pg';
const { Pool } = pkg;

// Configuration
const TEST_MODE = false;  // Running in production mode
const TEST_JOB_LIMIT = 5;
const EXPORT_DATA = true;

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

// Hunter.io API Configuration
const HUNTER_API_KEY = '8257696b56b9d35fe21a3d546e801e635a8b14a7';
const DOMAIN_SEARCH_API_URL = 'https://api.hunter.io/v2/domain-search';
const API_TIMEOUT_MS = 30000;
const BATCH_PAUSE_MS = 5000;
const CACHE_MAX_AGE_DAYS = 30;

// IMPORTANT: Set this to true to disable caching and force fresh Hunter API calls for each company
// This ensures we don't get the same contacts for different companies
const DISABLE_COMPANY_CACHE = true;

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
    "Restaurant Associates", "Source One Hospitality", "STARR", "Ten Five Hospitality",
    "The Goodkind Group", "Tuttle Hospitality", "Willow Tree Recruiting",
    // Adding Washington variants
    "washington", "washington dc", "washington d.c.", "washington d c"
].map(name => name.toLowerCase()));

// List of partial match exclusions (for companies with variations like "Whole Foods Market", etc.)
const PARTIAL_EXCLUSIONS = [
    "whole foods"
].map(name => name.toLowerCase());

// Force fresh companies
const FORCE_FRESH_COMPANIES = new Set([
    "fish cheeks", "fish cheeks noho", "fish cheeks - noho"
].map(name => name.toLowerCase()));

// In-memory cache
const companyCache = new Map();

// Helper functions
const timeout = (ms) => new Promise((_, reject) => setTimeout(() => reject(new Error(`Operation timed out after ${ms}ms`)), ms));
const delay = (ms) => new Promise(resolve => setTimeout(resolve, ms));
const now = () => new Date().toISOString();
const isStale = (timestamp) => {
    const cacheDate = new Date(timestamp);
    const ageInDays = (new Date() - cacheDate) / (1000 * 60 * 60 * 24);
    return ageInDays > CACHE_MAX_AGE_DAYS;
};

// Helper function to clean special characters but keep basic punctuation
function cleanSpecialCharacters(text) {
    if (!text) return '';
    // Keep only alphanumeric, spaces, and basic punctuation
    return text.replace(/[^\w\s.,&'-]/g, '');
}

// List of common country-specific TLDs that aren't US-based
const COUNTRY_TLDS = [
    // European countries
    '.uk', '.co.uk', '.ac.uk', '.org.uk', '.eu', '.de', '.fr', '.es', '.it', '.nl', '.be', '.dk', 
    '.se', '.no', '.fi', '.is', '.ie', '.ch', '.at', '.pt', '.pl', '.cz', '.sk', '.hu', '.ro', 
    '.bg', '.gr', '.ru', '.by', '.ua', '.hr', '.si', '.rs', '.me', '.lu', '.li', '.mt', '.cy',
    
    // Asia Pacific
    '.cn', '.jp', '.kr', '.hk', '.tw', '.sg', '.in', '.my', '.id', '.th', '.vn', '.ph', '.au', 
    '.nz', '.fj', '.pk', '.bd', '.kz', '.np', '.lk',
    
    // Americas (excluding .us)
    '.ca', '.mx', '.br', '.ar', '.cl', '.pe', '.ve', '.ec', '.bo', '.py', '.uy', '.cr',
    '.gt', '.pa', '.do', '.cu', '.hn', '.sv', '.ni', '.bs', '.tt', '.jm', '.ht', '.pr',
    // Note: .co is excluded as it's commonly used in the US as an alternative to .com
    
    // Africa & Middle East
    '.za', '.eg', '.ma', '.ng', '.ke', '.gh', '.tz', '.il', '.sa', '.ae', '.qa', '.kw', '.bh',
    '.om', '.jo', '.lb', '.dz', '.tn', '.zm', '.zw', '.et', '.mu', '.re',
    
    // City TLDs (mostly international)
    '.london', '.paris', '.berlin', '.moscow', '.tokyo', '.dubai', '.amsterdam', '.vienna',
    '.barcelona', '.istanbul', '.sydney', '.melbourne', '.toronto', '.quebec', '.rio',
    
    // Generic internationalized TLDs
    '.asia', '.international', '.global', '.world', '.international',
    
    // Common second-level domains in other countries
    '.com.au', '.co.nz', '.co.jp', '.co.uk', '.co.za', '.co.in', '.com.sg', '.com.my',
    '.com.br', '.com.mx', '.com.ar', '.com.cn', '.com.hk', '.com.tw'
];

// Generic email patterns to deprioritize
const GENERIC_EMAIL_PATTERNS = [
    'info@', 'contact@', 'hello@', 'admin@', 'support@', 
    'office@', 'mail@', 'inquiry@', 'general@', 'sales@',
    'help@', 'service@', 'hr@', 'jobs@', 'careers@',
    'team@', 'marketing@', 'press@', 'media@', 'events@'
];

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

async function loadCache() {
    // Skip loading cache if disabled
    if (DISABLE_COMPANY_CACHE) {
        log.info('⚠️ CACHE DISABLED: Skipping cache loading');
        companyCache.clear();
        return;
    }
    
    try {
        log.info('Loading cache from default KeyValueStore...');
        const store = await KeyValueStore.open();
        log.info(`Using KeyValueStore ID: ${store.id}`);
        const data = await store.getValue('company-cache-data');
        if (!data) {
            log.info('No cache data found, starting with empty cache.');
            return;
        }
        
        let loadedCount = 0;
        let staleCount = 0;
        let emptyEmailsCount = 0;
        let malformedCount = 0;
        let skippedDuplicates = 0;
        let forcedFreshCount = 0;
        
        // Track which companies we're loading to avoid duplicate variations
        const loadedCompanies = new Set();
        
        Object.entries(data).forEach(([key, value]) => {
            // Basic validation
            if (!value || typeof value !== 'object' || !value.timestamp) {
                log.info(`Skipping malformed cache entry (missing timestamp): ${key}`);
                malformedCount++;
                return;
            }
            
            // Check if stale
            if (isStale(value.timestamp)) {
                log.info(`Skipping stale cache entry: ${key}`);
                staleCount++;
                return;
            }
            
            // Validate emails array
            if (!value.emails || !Array.isArray(value.emails)) {
                log.info(`Skipping malformed cache entry (invalid emails array): ${key}`);
                malformedCount++;
                return;
            }
            
            // Skip empty emails
            if (value.emails.length === 0) {
                log.info(`Skipping cache entry with empty emails: ${key}`);
                emptyEmailsCount++;
                return;
            }
            
            // Validate each email object
            let hasMalformedEmail = false;
            for (const email of value.emails) {
                if (!email || typeof email !== 'object' || !email.email) {
                    hasMalformedEmail = true;
                    break;
                }
            }
            
            if (hasMalformedEmail) {
                log.info(`Skipping cache entry with malformed email objects: ${key}`);
                malformedCount++;
                return;
            }
            
            // Check for forced fresh company
            if (FORCE_FRESH_COMPANIES.has(key.toLowerCase())) {
                log.info(`Skipping force-fresh company: ${key}`);
                forcedFreshCount++;
                return;
            }
            
            // Add original company info if missing
            if (!value.originalCompany) {
                value.originalCompany = key.split(':')[0]; // Extract company from key
            }
            
            // Check for company variations to avoid loading duplicate data
            const companyPart = key.split(':')[0].toLowerCase();
            if (loadedCompanies.has(companyPart)) {
                log.info(`Skipping duplicate company variation: ${key}`);
                skippedDuplicates++;
                return;
            }
            
            // All checks passed, add to cache
            companyCache.set(key, value);
            loadedCompanies.add(companyPart);
            loadedCount++;
        });
        
        log.info(`Loaded ${loadedCount} fresh cache entries, skipped ${staleCount} stale, ${emptyEmailsCount} empty, ${malformedCount} malformed, ${skippedDuplicates} duplicates, ${forcedFreshCount} forced fresh.`);
        log.info(`Cache keys: ${Array.from(companyCache.keys()).join(', ')}`);
    } catch (error) {
        log.error(`Error loading cache: ${error.message}`);
    }
}

async function clearCache() {
    try {
        log.info('Clearing company cache...');
        
        // Clear in-memory cache
        companyCache.clear();
        
        // Clear persisted cache
        const store = await KeyValueStore.open();
        log.info(`Clearing cache from KeyValueStore ID: ${store.id}`);
        await store.setValue('company-cache-data', null);
        
        log.info('Cache has been cleared successfully');
        return true;
    } catch (error) {
        log.error(`Error clearing cache: ${error.message}`);
        return false;
    }
}

async function saveCache() {
    // Skip saving cache if disabled
    if (DISABLE_COMPANY_CACHE) {
        log.info('⚠️ CACHE DISABLED: Skipping cache saving');
        return;
    }
    
    try {
        log.info(`Saving ${companyCache.size} cache entries to default KeyValueStore...`);
        
        // Convert to object for storage
        const cacheObject = {};
        let entriesWithEmails = 0;
        let entriesPerSource = {};
        
        companyCache.forEach((value, key) => {
            // Validate before saving
            if (value && value.emails && Array.isArray(value.emails) && value.emails.length > 0) {
                cacheObject[key] = value;
                entriesWithEmails++;
                
                // Track counts by source
                const source = value.source || 'unknown';
                entriesPerSource[source] = (entriesPerSource[source] || 0) + 1;
            } else {
                log.info(`Not saving invalid cache entry: ${key}`);
            }
        });
        
        const store = await KeyValueStore.open();
        log.info(`Saving to KeyValueStore ID: ${store.id}`);
        await store.setValue('company-cache-data', cacheObject);
        
        // Log stats about what was saved
        log.info(`Cache saved successfully: ${entriesWithEmails} entries with emails out of ${companyCache.size} total entries`);
        log.info(`Entries by source: ${JSON.stringify(entriesPerSource)}`);
    } catch (error) {
        log.error(`Error saving cache: ${error.message}`);
    }
}

/**
 * Checks if an email has a non-US country-specific TLD
 * @param {string} email - The email to check
 * @returns {boolean} - True if the email should be filtered out (non-US TLD), false otherwise
 */
function hasNonUSTld(email) {
    if (!email || typeof email !== 'string') {
        return false; // If no email provided, don't filter
    }
    
    // Convert email to lowercase for case-insensitive matching
    const lowerEmail = email.toLowerCase();
    
    // Check if the email ends with any of the country-specific TLDs
    return COUNTRY_TLDS.some(tld => {
        return lowerEmail.endsWith(tld);
    });
}

/**
 * No longer filters emails based on TLD - returns all emails
 * @param {Array} emails - Array of email objects
 * @returns {Array} - The same array of email objects
 */
function filterNonUSEmails(emails) {
    if (!emails || !Array.isArray(emails)) {
        return [];
    }
    
    // Return all emails without filtering
    log.info(`[TLD Filter] Keeping all ${emails.length} emails regardless of domain`);
    return emails;
}

/**
 * Checks if an email is a generic/role-based email rather than a personal one
 * @param {string} email - The email to check
 * @returns {boolean} - True if the email is generic, false if it's likely personal
 */
function isGenericEmail(email) {
    if (!email || typeof email !== 'string') {
        return true; // Consider empty emails as generic
    }
    
    const lowerEmail = email.toLowerCase();
    
    // Check if it matches any generic patterns
    return GENERIC_EMAIL_PATTERNS.some(pattern => lowerEmail.includes(pattern));
}

/**
 * Calculate a score for an email based on various factors even when job title is absent
 * @param {Object} email - Email object from Hunter API
 * @returns {number} - Score value (lower is better)
 */
function calculateEmailScore(email) {
    if (!email || !email.value) {
        return 1000; // Very low score for invalid emails
    }
    
    let score = 500; // Base score
    
    // Process job title if available (highest priority factor)
    const title = email.position || email.position_raw || '';
    if (title && title.trim()) {
        score = getTitlePriority(title);
        return score; // Return early if we have a title match
    }
    
    // No title available, use other factors
    
    // Prefer personal emails over generic ones
    if (isGenericEmail(email.value)) {
        score += 200;
    } else {
        score -= 100;
    }
    
    // Prefer emails with names over unnamed contacts
    if (email.first_name || email.last_name) {
        score -= 50;
    } else {
        score += 50;
    }
    
    // Use confidence if available
    if (typeof email.confidence === 'number') {
        // Higher confidence = lower score (better)
        score -= (email.confidence / 2);
    }
    
    // Prefer higher quality types
    if (email.type) {
        if (email.type === 'personal') {
            score -= 75;
        } else if (email.type === 'generic') {
            score += 25;
        }
    }
    
    return score;
}

/**
 * Process emails from Hunter API with improved prioritization and filtering
 * @param {Array|Object} emailsData - Data from Hunter API or array of emails
 * @returns {Array} - Sorted contacts with highest priority first
 */
function processEmails(emailsData) {
    if (!emailsData) {
        log.info('No email data to process');
        return [];
    }
    
    try {
        // Handle both array input (from older code) and object input (API response)
        let emails = [];
        
        // Check if we're dealing with an Array (direct emails) or Object (full API response)
        if (Array.isArray(emailsData)) {
            log.info(`Processing ${emailsData.length} emails (array format)`);
            emails = emailsData;
        } else if (emailsData.data && emailsData.data.emails && Array.isArray(emailsData.data.emails)) {
            log.info(`Processing ${emailsData.data.emails.length} emails for domain: ${emailsData.data.domain || 'unknown'}`);
            emails = emailsData.data.emails;
        } else {
            log.info('Invalid email data format');
            return [];
        }
        
        if (emails.length === 0) {
            return [];
        }
        
        // Filter out non-US emails (optional, enable or disable as needed)
        const enableTldFiltering = true; // Set to false to disable TLD filtering
        
        let processedEmails = emails;
        if (enableTldFiltering) {
            // Keep track of original count
            const originalCount = emails.length;
            
            // Filter out emails with non-US TLDs
            processedEmails = filterNonUSEmails(emails);
            
            // Record filtered emails
            const filteredCount = originalCount - processedEmails.length;
            
            // Log TLD filtering information
            if (filteredCount > 0) {
                const domain = emailsData.data ? emailsData.data.domain || 'unknown' : 'unknown';
                log.info(`[TLD Filter] Domain: ${domain} | Filtered out ${filteredCount}/${originalCount} non-US emails`);
            }
            
            // Use original list if filtering removed all emails
            if (processedEmails.length === 0 && originalCount > 0) {
                log.info(`[TLD Filter] All emails were filtered out, using unfiltered list`);
                processedEmails = emails;
            }
        }
        
        // Log the emails we're processing
        log.info(`Processing ${processedEmails.length} email contacts`);
        if (processedEmails.length > 0) {
            log.info(`Sample email structure: ${JSON.stringify(processedEmails[0])}`);
        }
        
        // Enhanced email handling - don't filter out by email.value as this can remove valid emails
        // Use map directly to normalize the data structure
        const scoredEmails = processedEmails.map(email => {
            // Handle multiple possible formats - ensure we catch all valid email formats
            const emailValue = email.value || email.email || '';
            const firstName = email.first_name || '';
            const lastName = email.last_name || '';
            const position = email.position || email.position_raw || '';
            const confidence = email.confidence || 0;
            
            // Skip invalid emails during mapping
            if (!emailValue) {
                log.debug(`Skipping email without address: ${JSON.stringify(email)}`);
                return null;
            }
            
            const score = calculateEmailScore(email);
            
            return { 
                name: (firstName && lastName) ? 
                    `${firstName} ${lastName}`.trim() : 
                    (firstName || lastName || 'Unknown'),
                title: position || 'N/A',
                email: emailValue,
                confidence: confidence,
                priority: score  // Store score for debugging and sorting
            };
        });
        
        // Filter out null entries (emails without addresses) and sort by score (lower is better)
        const validEmails = scoredEmails.filter(email => email !== null);
        
        if (validEmails.length === 0) {
            log.info('No valid emails found after processing');
            return [];
        }
        
        // Sort by score (lower is better)
        const sortedEmails = validEmails.sort((a, b) => a.priority - b.priority);
        
        // Log sorted results for debugging
        log.info(`Email priority sorting results:`);
        sortedEmails.slice(0, 5).forEach((email, index) => {
            const matchedTerm = email.priority < TITLE_PRIORITY.length ? 
                TITLE_PRIORITY[email.priority] : 'No match';
            log.info(`  ${index+1}. ${email.name}, ${email.title} - Priority: ${email.priority} (${matchedTerm})`);
        });
        
        return sortedEmails;
    } catch (error) {
        log.error(`Error processing emails: ${error.message}`);
        return [];
    }
}

async function getCompanyInfoWithSource(companyName, locationName = '', source = 'company') {
    if (!companyName || companyName === 'Unknown' || companyName.startsWith('Excluded:')) {
        log.info(`Skipping ${source} search for ${companyName || 'unknown'} name`);
        return { linkedin: 'N/A', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source };
    }
    
    // Warn if location is provided - we should avoid using locations in email searches
    if (locationName && locationName.trim() !== '') {
        log.info(`WARNING: Location "${locationName}" was provided to getCompanyInfoWithSource for "${companyName}". Location should NOT be used for email searches to avoid incorrect TLD matches.`);
    }
    
    // Clean special characters from company name
    const withoutSpecialChars = cleanSpecialCharacters(companyName);
    // Preserve capitalization for company names like "STARR Restaurants"
    const cleanedName = cleanCompanyName(withoutSpecialChars);
    
    // Log both original and cleaned versions
    log.info(`${source} name: "${companyName}" cleaned to "${cleanedName}"`);
    
    // For comparison purposes, use lowercase but preserve spaces
    const lowerCleanedName = cleanedName.toLowerCase();
    
    // Create a variant with spaces removed only for exclusion list checks
    // We don't use this normalized version for actual API searches
    const normalizedName = lowerCleanedName.replace(/\s+/g, '');
    if (normalizedName !== lowerCleanedName.replace(/\s+/g, '')) {
        log.info(`Normalized version (for exclusion checks only): "${normalizedName}"`);
    }
    
    // Check for exact match in exclusion list (with and without spaces)
    if (EXCLUDED_COMPANIES.has(lowerCleanedName) || 
        Array.from(EXCLUDED_COMPANIES).some(excluded => normalizedName.includes(excluded.replace(/\s+/g, '')))) {
        log.info(`Skipping exactly excluded ${source}: "${companyName}" (normalized: "${normalizedName}")`);
        return { linkedin: 'Excluded', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source };
    }
    
    // Check for partial matches with normalized spaces (like "WholeFoodsMarket" containing "wholefoods")
    for (const partialTerm of PARTIAL_EXCLUSIONS) {
        const normalizedTerm = partialTerm.replace(/\s+/g, '');
        // Check both regular and normalized versions
        if (lowerCleanedName.includes(partialTerm) || normalizedName.includes(normalizedTerm)) {
            log.info(`Skipping partially excluded ${source}: "${companyName}" (contains "${partialTerm}", normalized: "${normalizedTerm}")`);
            return { linkedin: 'Excluded', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source };
        }
    }
    const shouldForceRefresh = FORCE_FRESH_COMPANIES.has(lowerCleanedName);
    // Make the cache key unique by including the full company name, not just the cleaned name
    const cacheKey = `${companyName.toLowerCase()}:${source}`;
    
    // Also check if we should refresh the original cleaned name key
    if (shouldForceRefresh) {
        if (companyCache.has(cacheKey)) {
            companyCache.delete(cacheKey);
        }
        // Also delete any keys that might have this company as part of their key
        for (const key of companyCache.keys()) {
            if (key.toLowerCase().includes(lowerCleanedName)) {
                log.info(`Force refreshing related cache key: "${key}"`);
                companyCache.delete(key);
            }
        }
    }
    
    // Check cache with the more precise key - unless cache is disabled
    const useCaching = !DISABLE_COMPANY_CACHE && !shouldForceRefresh;
    
    if (useCaching && companyCache.has(cacheKey)) {
        const cachedData = companyCache.get(cacheKey);
        if (cachedData.emails && Array.isArray(cachedData.emails) && cachedData.emails.length > 0) {
            log.info(`Cache hit for exact key "${cacheKey}"`);
            
            // Add info about cache contents for debugging
            const emailDebug = cachedData.emails.map((e, i) => 
                `${i+1}. ${e.name || 'Unknown'}: ${e.email || 'N/A'} (${e.title || 'N/A'})`).join(', ');
            log.info(`CACHE DEBUG: ${cacheKey} contains emails: ${emailDebug}`);
            
            return cachedData;
        }
        companyCache.delete(cacheKey);
    }
    
    if (DISABLE_COMPANY_CACHE) {
        log.info(`Cache is disabled - making fresh API call for "${companyName}"`);
    }
    try {
        log.info(`Fetching ${source} data for "${companyName}"...`);
        await delay(1000);
        
        // Ensure we're only using the company name for searches - NEVER include location information
        // This prevents incorrect TLD matches (e.g., searching for "Brooklyn" and getting brooklyn.be emails)
        
        // Use the properly cleaned company name but preserve capitalization
        // This helps with capitalized names like "STARR Restaurants"
        const cleanCompanyForSearch = cleanedName.trim();
        const apiUrl = `${DOMAIN_SEARCH_API_URL}?company=${encodeURIComponent(cleanCompanyForSearch)}&limit=10&api_key=${HUNTER_API_KEY}`;
        log.info(`API request URL (${source}): ${apiUrl}`);
        const response = await Promise.race([
            fetch(apiUrl, { method: 'GET', headers: { 'Content-Type': 'application/json' } }),
            timeout(API_TIMEOUT_MS),
        ]);
        if (!response.ok) {
            const errorText = await response.text();
            log.error(`Hunter API error for "${companyName}" (${source}): ${response.status} - ${errorText}`);
            if (response.status === 429) {
                await delay(10000);
            }
            throw new Error(`Hunter API returned error ${response.status}: ${errorText}`);
        }
        const data = await response.json();
        if (!data || !data.data) {
            throw new Error('Invalid API response: missing data object');
        }
        
        log.info(`[Hunter Response] Successfully parsed JSON for ${companyName} (${source})`);
        
        if (!data || !data.data) {
            log.error(`[Hunter Response Error] Invalid API response for ${companyName} (${source}): missing data object. Response: ${JSON.stringify(data)}`);
            throw new Error('Invalid API response: missing data object');
        }
        
        // Check if there are search results we can use
        if (data.data.results && Array.isArray(data.data.results) && data.data.results.length > 0) {
            log.info(`Hunter API returned ${data.data.results.length} potential companies for "${companyName}"`);
            
            // Log all results for debugging - safely check properties
            data.data.results.forEach((result, index) => {
                const hasEmails = result && result.emails && Array.isArray(result.emails);
                const emailCount = hasEmails ? result.emails.length : 0;
                const company = result && result.company ? result.company : 'Unknown';
                const domain = result && result.domain ? result.domain : 'N/A';
                
                log.info(`Result #${index+1}: "${company}" - Domain: ${domain}, Emails: ${emailCount}`);
            });
            
            // Find the first result with emails - with defensive checks
            let bestResultIndex = -1;
            for (let i = 0; i < data.data.results.length; i++) {
                const result = data.data.results[i];
                if (result && result.emails && Array.isArray(result.emails) && result.emails.length > 0) {
                    bestResultIndex = i;
                    break;
                }
            }
            
            // If found a result with emails, use it
            if (bestResultIndex >= 0) {
                const bestResult = data.data.results[bestResultIndex];
                const hasEmails = bestResult && bestResult.emails && Array.isArray(bestResult.emails);
                const emailCount = hasEmails ? bestResult.emails.length : 0;
                
                log.info(`Selected result #${bestResultIndex+1} "${bestResult.company || 'Unknown'}" with ${emailCount} emails`);
                
                // IMPORTANT: Add company information to EACH email object BEFORE processing
                // This ensures the original company stays with each contact
                if (hasEmails) {
                    // Add company information to each email object before processing
                    bestResult.emails = bestResult.emails.map(email => ({
                        ...email,
                        _originalCompany: bestResult.company || companyName,
                        _originalDomain: bestResult.domain,
                        _sourceTime: Date.now()
                    }));
                    
                    log.info(`Added company identification to ${bestResult.emails.length} emails for "${bestResult.company || companyName}"`);
                }
                
                const processedEmails = hasEmails ? processEmails(bestResult.emails) : [];
                
                // Log all the processed emails we have for this company
                if (processedEmails.length > 0) {
                    log.info(`ALL processed emails for company "${bestResult.company || companyName}":`);
                    processedEmails.forEach((email, idx) => {
                        log.info(`  ${idx+1}. ${email.name}, ${email.title}, ${email.email} - Priority: ${email.priority} - Company: ${email._originalCompany || 'unknown'}`);
                    });
                }
                
                const result = {
                    linkedin: bestResult.linkedin || 'N/A',
                    domain: bestResult.domain || 'N/A',
                    size: bestResult.employees_count || bestResult.headcount || 'N/A',
                    emails: processedEmails, // Keep ALL emails, not just top 3
                    timestamp: now(),
                    source: `${source}_result_${bestResultIndex+1}`
                };
                return result;
            } else {
                log.info(`No results with emails found among ${data.data.results.length} companies - using primary result`);
            }
        }
        
        // If no results array or no results with emails, use the primary data
        const companyData = data.data;
        // Add defensive checks for emails property
        const hasEmails = companyData && companyData.emails && Array.isArray(companyData.emails);
        
        // IMPORTANT: Add company information to EACH email object BEFORE processing
        // This ensures the original company stays with each contact
        if (hasEmails) {
            // Add company identification to each email before processing
            companyData.emails = companyData.emails.map(email => ({
                ...email,
                _originalCompany: companyData.organization || companyName,
                _originalDomain: companyData.domain,
                _sourceTime: Date.now()
            }));
            
            log.info(`Added company identification to ${companyData.emails.length} emails for "${companyData.organization || companyName}"`);
        }
        
        const processedEmails = hasEmails ? processEmails(companyData.emails) : [];
        
        // Log all the processed emails we have for this company
        if (processedEmails.length > 0) {
            log.info(`ALL processed emails for company "${companyData.organization || companyName}":`);
            processedEmails.forEach((email, idx) => {
                log.info(`  ${idx+1}. ${email.name}, ${email.title}, ${email.email} - Priority: ${email.priority} - Company: ${email._originalCompany || 'unknown'}`);
            });
        }
        
        const result = {
            linkedin: companyData.linkedin || 'N/A',
            domain: companyData.domain || 'N/A',
            size: companyData.headcount || 'N/A',
            emails: processedEmails, // Keep ALL emails, not just top 3
            timestamp: now(),
            source
        };
        const emailsLog = result.emails.length > 0 
            ? result.emails.map(e => `${e.name}, ${e.title}, ${e.email}`).join('; ') 
            : 'None';
        log.info(`Found data for "${companyName}" (${source}): LinkedIn=${result.linkedin}, Domain=${result.domain}, Emails=${emailsLog}`);
        if (result.emails.length > 0) {
            // Store information about which company generated these emails
            result.originalCompany = companyName;
            
            // Only store in cache if caching is enabled
            if (!DISABLE_COMPANY_CACHE) {
                companyCache.set(cacheKey, result);
                
                // Debug: how many entries in the cache
                log.info(`Cache now contains ${companyCache.size} entries. Recent key: ${cacheKey}`);
                
                // Save cache to storage
                await saveCache();
            } else {
                log.info(`Cache disabled - not storing result for "${companyName}"`);
            }
        } else {
            log.info(`Not caching result for "${companyName}" (${source}) due to empty emails list`);
        }
        return result;
    } catch (error) {
        log.error(`Error fetching ${source} data for "${companyName}": ${error.message}`);
        if (source === 'company' && locationName && locationName !== companyName) {
            log.info(`No data for "${companyName}" (${source}), trying location "${locationName}"...`);
            return await getCompanyInfoWithSource(locationName, '', 'location');
        }
        return { linkedin: 'Error', domain: 'N/A', size: 'N/A', emails: [], timestamp: now(), source };
    }
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

async function getCompanyInfo(rawCompanyName, rawLocation = '') {
    const { name: cleanedCompany } = parseCompanyAndLocation(rawCompanyName);
    let allResults = [];
    
    // ALWAYS try with main company name
    log.info(`Searching Hunter API with primary company name: "${cleanedCompany}"`);
    const companyInfo = await getCompanyInfoWithSource(cleanedCompany, rawLocation, 'company');
    allResults.push({ source: 'primary', data: companyInfo });
    log.info(`Found ${companyInfo.emails.length} emails with primary company name "${cleanedCompany}"`);
    
    // ALWAYS also try with the whole location string if it exists and is different
    if (rawLocation && rawLocation !== cleanedCompany) {
        // Clean special characters from the location string
        const cleanedLocation = cleanSpecialCharacters(rawLocation);
        
        // Skip if the location is just "Restaurant Group" or another generic term
        // Define common generic terms here to avoid scope issues
        const commonGenericTerms = [
            'restaurant group', 'hospitality group', 'restaurant', 'hospitality', 
            'group', 'consulting', 'management'
        ];
        
        if (commonGenericTerms.includes(cleanedLocation.toLowerCase()) || 
            cleanedLocation.toLowerCase() === 'restaurant group') {
            log.info(`Location "${cleanedLocation}" is a generic term - skipping API call`);
            allResults.push({ 
                source: 'location', 
                data: { 
                    linkedin: 'N/A', 
                    domain: 'N/A', 
                    size: 'N/A', 
                    emails: [], 
                    timestamp: now(), 
                    source: 'generic_term_location' 
                } 
            });
        } else {
            // Check if the location contains any excluded company names before proceeding
            const normalizedLocation = cleanedLocation.toLowerCase().replace(/\s+/g, '');
            let isExcluded = false;
            
            // Check for partial matches first (e.g., "whole foods")
            for (const partialTerm of PARTIAL_EXCLUSIONS) {
                const normalizedTerm = partialTerm.replace(/\s+/g, '');
                if (normalizedLocation.includes(normalizedTerm)) {
                    log.info(`Location contains excluded company "${partialTerm}" - skipping API call`);
                    isExcluded = true;
                    allResults.push({ 
                        source: 'location', 
                        data: { 
                            linkedin: 'Excluded', 
                            domain: 'N/A', 
                            size: 'N/A', 
                            emails: [], 
                            timestamp: now(), 
                            source: 'excluded_location' 
                        } 
                    });
                    break;
                }
            }
            
            // Also check the full exclusion list if not already excluded
            if (!isExcluded && Array.from(EXCLUDED_COMPANIES).some(excluded => 
                normalizedLocation.includes(excluded.replace(/\s+/g, '')))) {
                log.info(`Location contains excluded company - skipping API call`);
                isExcluded = true;
                allResults.push({ 
                    source: 'location', 
                    data: { 
                        linkedin: 'Excluded', 
                        domain: 'N/A', 
                        size: 'N/A', 
                        emails: [], 
                        timestamp: now(), 
                        source: 'excluded_location' 
                    } 
                });
            }
            
            // Only proceed with API call if not excluded
            if (!isExcluded) {
                log.info(`Searching Hunter API with full location: "${cleanedLocation}"`);
                const locationInfo = await getCompanyInfoWithSource(cleanedLocation, '', 'full_location');
                allResults.push({ source: 'location', data: locationInfo });
                log.info(`Found ${locationInfo.emails.length} emails with full location "${cleanedLocation}"`);
            }
        }
    }
    
    // Extract and ALWAYS try potential company names from the address
    const potentialCompanies = extractPotentialCompaniesFromAddress(rawLocation);
    log.info(`Extracted ${potentialCompanies.length} potential companies from address: ${potentialCompanies.join(', ')}`);
    
    // Process each potential company through parseCompanyAndLocation first to fix spacing issues
    const parsedPotentialCompanies = potentialCompanies.map(company => {
        const { name } = parseCompanyAndLocation(company);
        return { original: company, parsed: name };
    }).filter(item => item.parsed !== 'Unknown');
    
    log.info(`Parsed ${parsedPotentialCompanies.length} valid potential companies: ${
        parsedPotentialCompanies.map(item => `${item.original} → ${item.parsed}`).join(', ')
    }`);
    
    for (const { original: potentialCompany, parsed: parsedCompany } of parsedPotentialCompanies) {
        // Skip if it's too similar to what we already tried
        if (parsedCompany.toLowerCase() === cleanedCompany.toLowerCase() || 
            parsedCompany.toLowerCase() === rawLocation.toLowerCase()) {
            continue;
        }
        
        // Skip excluded companies in potential matches
        const normalizedPotential = parsedCompany.toLowerCase().replace(/\s+/g, '');
        let isExcluded = false;
        
        // Check partial exclusions
        for (const partialTerm of PARTIAL_EXCLUSIONS) {
            const normalizedTerm = partialTerm.replace(/\s+/g, '');
            if (normalizedPotential.includes(normalizedTerm)) {
                log.info(`Potential company "${potentialCompany}" (parsed: "${parsedCompany}") contains excluded term "${partialTerm}" - skipping`);
                isExcluded = true;
                const index = parsedPotentialCompanies.findIndex(p => p.original === potentialCompany);
                allResults.push({ 
                    source: `excluded_potential_${index >= 0 ? index : 'unknown'}`, 
                    data: { 
                        linkedin: 'Excluded', 
                        domain: 'N/A', 
                        size: 'N/A', 
                        emails: [], 
                        timestamp: now(), 
                        source: 'excluded_potential' 
                    } 
                });
                break;
            }
        }
        
        // Check full exclusions
        if (!isExcluded && Array.from(EXCLUDED_COMPANIES).some(excluded => 
            normalizedPotential.includes(excluded.replace(/\s+/g, '')))) {
            log.info(`Potential company "${potentialCompany}" (parsed: "${parsedCompany}") matches exclusion list - skipping`);
            isExcluded = true;
            const index = parsedPotentialCompanies.findIndex(p => p.original === potentialCompany);
            allResults.push({ 
                source: `excluded_potential_${index >= 0 ? index : 'unknown'}`, 
                data: { 
                    linkedin: 'Excluded', 
                    domain: 'N/A', 
                    size: 'N/A', 
                    emails: [], 
                    timestamp: now(), 
                    source: 'excluded_potential' 
                } 
            });
        }
        
        // Only proceed if not excluded
        if (!isExcluded) {
            log.info(`Searching Hunter API with potential company from address: "${parsedCompany}" (original: "${potentialCompany}")`);
            const index = parsedPotentialCompanies.findIndex(p => p.original === potentialCompany);
            const sourceId = `potential_${index >= 0 ? index : 'unknown'}`;
            const potentialInfo = await getCompanyInfoWithSource(parsedCompany, '', sourceId);
            allResults.push({ source: sourceId, data: potentialInfo });
            log.info(`Found ${potentialInfo.emails.length} emails with potential company "${parsedCompany}"`);
        }
    }
    
    // ALWAYS merge all results to get the most comprehensive set
    // This ensures we get both unit employees and corporate employees
    const mergedResult = {
        linkedin: '',
        domain: '',
        size: 'N/A',
        emails: [],
        timestamp: now(),
        source: 'merged',
        sourcesWithEmails: 0
    };
    
    // Track already added emails to avoid duplicates
    const addedEmails = new Set();
    const linkedins = new Set();
    const domains = new Set();
    
    // First pass: collect all unique LinkedIn URLs and domains
    for (const result of allResults) {
        if (result.data.linkedin && result.data.linkedin !== 'N/A' && result.data.linkedin !== 'Excluded' && result.data.linkedin !== 'Error') {
            linkedins.add(result.data.linkedin);
        }
        if (result.data.domain && result.data.domain !== 'N/A') {
            domains.add(result.data.domain);
        }
    }
    
    // Join all LinkedIn URLs and domains with semicolons
    mergedResult.linkedin = Array.from(linkedins).join('; ') || 'N/A';
    mergedResult.domain = Array.from(domains).join('; ') || 'N/A';
    
    // Sort results - put ones with emails first to ensure best quality data first
    allResults.sort((a, b) => b.data.emails.length - a.data.emails.length);
    
    // Add emails from all sources
    for (const result of allResults) {
        // Track sources that contributed emails
        if (result.data.emails.length > 0) {
            mergedResult.sourcesWithEmails++;
        }
        
        // Get company size from best source if not set
        if (mergedResult.size === 'N/A' && result.data.size !== 'N/A') {
            mergedResult.size = result.data.size;
        }
        
        // Add emails without duplicates
        for (const email of result.data.emails) {
            const emailKey = email.email.toLowerCase();
            if (!addedEmails.has(emailKey)) {
                addedEmails.add(emailKey);
                // Add source information to each email for tracking
                mergedResult.emails.push({
                    ...email,
                    source: result.source
                });
            }
        }
    }
    
    // Sort emails by job title priority
    mergedResult.emails.sort((a, b) => getTitlePriority(a.title) - getTitlePriority(b.title));
    
    log.info(`RESULTS SUMMARY: Found ${mergedResult.emails.length} unique emails from ${mergedResult.sourcesWithEmails} search strategies`);
    log.info(`LinkedIn URLs: ${mergedResult.linkedin}`);
    log.info(`Domains: ${mergedResult.domain}`);
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
                        url, job_details, linkedin, domain, company_size, date_added
                    ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, NOW())
                    ON CONFLICT (url) DO UPDATE SET 
                        title = EXCLUDED.title,
                        company = EXCLUDED.company,
                        parent_company = EXCLUDED.parent_company,
                        location = EXCLUDED.location,
                        salary = EXCLUDED.salary,
                        job_details = EXCLUDED.job_details,
                        linkedin = EXCLUDED.linkedin,
                        domain = EXCLUDED.domain,
                        company_size = EXCLUDED.company_size,
                        last_updated = NOW()
                    RETURNING id`;

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
                    job.size || null,
                ]);

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
        log.info(`Batch size ${exportBatch.length} reached, exporting...`);
        try {
            await exportToPostgres(exportBatch);
            exportBatch = []; // Clear the batch after successful export
            log.info('Batch export completed successfully');
        } catch (error) {
            log.error('Failed to export batch:', error);
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

        // Initialize state store and request queue
        const stateStore = await KeyValueStore.open();
        const state = await stateStore.getValue('SCRAPE_STATE') || { processedCount: 0 };
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
            maxRequestsPerMinute: TEST_MODE ? 2 : 6,
            // REMOVED launchContext and preNavigationHooks

            // Replace requestHandler with logic from the old snippet
            async requestHandler({ $, request, log }) { // Ensure enqueueLinks is available if needed, or remove if not used by snippet
                log.info(`Processing page ${request.url}`);
                
                // --- START: Logic from provided snippet --- 
                const jobCards = $('.ca-single-job-card');
                log.info(`Found ${jobCards.length} jobs on page ${request.url}`);
                
                // Assume stateStore is initialized outside
                const stateStore = await KeyValueStore.open(); 
                const state = await stateStore.getValue('SCRAPE_STATE') || { processedCount: 0 };

                // Assume existingDataset is initialized outside
                const existingDataset = await Dataset.open('culinary-jobs'); 
                
                // Assume existingUrls Set is initialized outside and populated if needed
                const existingUrls = new Set(); // Placeholder - this needs proper initialization

                // Assume processedJobsList array is initialized outside for batching
                // let processedJobsList = []; // Placeholder - this needs proper initialization
                // Note: exportBatch is already global, maybe use that instead? Using exportBatch for now.

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
                const cardsToProcess = TEST_MODE ? 
                    Math.min(TEST_JOB_LIMIT - (state.processedCount || 0), jobCards.length) : 
                    jobCards.length;
                    
                for (let i = 0; i < cardsToProcess; i++) {
                    const el = jobCards[i];
                    const jobUrl = ensureAbsoluteUrl($(el).attr('href')); // ensureAbsoluteUrl must be defined
                    if (!jobUrl || existingUrls.has(jobUrl)) {
                        if (jobUrl) log.info(`Skipping existing job: ${jobUrl}`);
                        continue;
                    }
                    const title = $(el).find('.job-title strong').text().trim() || 'Unknown';
                    const rawCompany = $(el).find('.text-body.text-ellipsis:not(.job-employment)').text().trim() || 'Unknown';
                    const { name: company } = parseCompanyAndLocation(rawCompany); // parseCompanyAndLocation must be defined
                    const fullAddress = $(el).find('.text-muted.text-ellipsis').text().trim() || 'N/A';
                    
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
                        try {
                            await delay(TEST_MODE ? 1000 : 2000); // delay must be defined
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
                                leadershipSection.find('a.text-body').each((i, leaderEl) => {
                                    const leader = $detail(leaderEl);
                                    const name = leader.find('.font-weight-bold').text().trim();
                                    const title = leader.find('p').text().trim() || 'N/A';
                                    if (name) leadership.push({ name, title });
                                });
                            }
                            
                            let contactInfo; // Declare contactInfo
                            if (parentCompany) {
                                log.info(`Using parent company "${parentCompany}" for contact search`);
                                const parentContactInfo = await getCompanyInfoWithSource(parentCompany, '', 'parent_company'); // getCompanyInfoWithSource must be defined
                                const companyContactInfo = await getCompanyInfoWithSource(listing.company, '', 'subsidiary_company');
                                
                                const hasParentEmails = parentContactInfo?.emails && Array.isArray(parentContactInfo.emails);
                                const hasCompanyEmails = companyContactInfo?.emails && Array.isArray(companyContactInfo.emails);
                                const parentEmailCount = hasParentEmails ? parentContactInfo.emails.length : 0;
                                const companyEmailCount = hasCompanyEmails ? companyContactInfo.emails.length : 0;
                                
                                log.info(`Parent company source: ${parentContactInfo.source || 'unknown'}, emails: ${parentEmailCount}`);
                                log.info(`Original company source: ${companyContactInfo.source || 'unknown'}, emails: ${companyEmailCount}`);
                                
                                const emailMap = new Map();
                                if (hasParentEmails) {
                                    for (const email of parentContactInfo.emails) {
                                        if (email?.email) { 
                                            const key = email.email.toLowerCase();
                                            if (!emailMap.has(key)) emailMap.set(key, {...JSON.parse(JSON.stringify(email)), source: 'parent_company'});
                                        }
                                    }
                                }
                                if (hasCompanyEmails) {
                                    for (const email of companyContactInfo.emails) {
                                        if (email?.email) { 
                                            const key = email.email.toLowerCase();
                                            if (!emailMap.has(key)) emailMap.set(key, {...JSON.parse(JSON.stringify(email)), source: 'subsidiary_company'});
                                        }
                                    }
                                }
                                
                                const combinedEmails = Array.from(emailMap.values())
                                    .sort((a, b) => getTitlePriority(a.title) - getTitlePriority(b.title)); // getTitlePriority must be defined
                                    
                                contactInfo = {
                                    linkedin: parentContactInfo.linkedin || companyContactInfo.linkedin || 'N/A',
                                    domain: parentContactInfo.domain || companyContactInfo.domain || 'N/A',
                                    size: parentContactInfo.size || companyContactInfo.size || 'N/A',
                                    emails: combinedEmails,
                                    timestamp: now(),
                                    source: parentEmailCount > 0 ? 'parent_company' : 'subsidiary_company'
                                };
                                log.info(`Combined contacts, ${combinedEmails.length} unique emails`);
                            } else {
                                log.info(`Getting contact info for "${listing.company}"`);
                                contactInfo = await getCompanyInfo(listing.company, ''); // getCompanyInfo must be defined
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
                                size: contactInfo.size || 'N/A',
                                dataSource: contactInfo.source || 'unknown',
                                dataDate: now(),
                                dateAdded: now(), 
                                _processId: Date.now()
                            };
                            
                            const verifiedDetail = JSON.parse(JSON.stringify(jobDetail));
                            jobDetailsArray.push(verifiedDetail);
                            log.info(`Processed job: ${listing.title} at ${listing.company} with ${verifiedDetail.emails.length} contacts`);
                            state.processedCount = (state.processedCount || 0) + 1;
                        } catch (error) {
                            log.error(`Error fetching details for ${listing.url}: ${error.message}`);
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
                                const dataToExport = JSON.parse(JSON.stringify(exportBatch));
                                await handleBatchExport(); // This function now uses the global exportBatch
                                log.info(`Cleared export batch after successful/attempted export.`);
                                // Note: handleBatchExport should clear the global exportBatch on success
                            }
                        } catch (error) {
                            log.error(`Failed to process batch: ${error.message}`);
                        }
                    }
                }
                
                log.info(`Jobs processed: ${state.processedCount}/${TEST_MODE ? TEST_JOB_LIMIT : (await stateStore.getValue('TOTAL_JOBS') || 2000)}`);
                
                if (TEST_MODE && state.processedCount >= TEST_JOB_LIMIT) {
                    log.info(`Test mode: Reached limit of ${TEST_JOB_LIMIT} jobs. Stopping crawler.`);
                    // await requestQueue.drop(); // This might be too abrupt, let current finish
                    return;
                }
                
                const nextPage = request.userData?.page || 1;
                const totalJobsTarget = TEST_MODE ? TEST_JOB_LIMIT : (await stateStore.getValue('TOTAL_JOBS') || 2000);
                
                if (state.processedCount < totalJobsTarget) {
                    const nextPageUrl = `https://culinaryagents.com/search/jobs?search%5Bcompensation%5D%5B%5D=salary&offset=${nextPage * 20}`;
                    log.info(`Queueing next page: ${nextPageUrl}`);
                    await delay(TEST_MODE ? 5000 : 30000);
                    await requestQueue.addRequest({ url: nextPageUrl, userData: { page: nextPage + 1 } });
                } else {
                    log.info(`Reached target of ${totalJobsTarget} jobs. No more pages will be queued.`);
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
        
        await saveCache(); // saveCache must be defined
        
        // Final export if any remaining jobs
        if (EXPORT_DATA && exportBatch.length > 0) { // Use global exportBatch
            log.info(`Exporting final batch of ${exportBatch.length} results...`);
            const dataToExport = JSON.parse(JSON.stringify(exportBatch)); 
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
        await pool.end();
        log.info('Database pool closed.');
    }
});

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