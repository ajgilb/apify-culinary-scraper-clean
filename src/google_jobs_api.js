/**
 * Google Jobs API integration using SearchAPI.io
 * This module provides functions to search for job listings using the Google Jobs API via SearchAPI.io
 */

/**
 * Searches for job listings using the Google Jobs API
 * @param {string} query - The search query (e.g., "restaurant chef united states")
 * @param {string} location - Optional location filter (e.g., "New York")
 * @param {string} nextPageToken - Optional token for pagination
 * @returns {Promise<Object>} - Job listings and pagination info
 */
async function searchJobs(query, location = '', nextPageToken = null) {
    const apiKey = process.env.SEARCH_API_KEY;
    
    if (!apiKey) {
        console.warn('SEARCH_API_KEY environment variable not found. Skipping Google Jobs search.');
        return { jobs: [], hasMore: false };
    }

    try {
        // Build the API URL
        let searchUrl = `https://www.searchapi.io/api/v1/search?engine=google_jobs&q=${encodeURIComponent(query)}&api_key=${apiKey}`;
        
        // Add location if provided
        if (location) {
            searchUrl += `&location=${encodeURIComponent(location)}`;
        }
        
        // Add pagination token if provided
        if (nextPageToken) {
            searchUrl += `&next_page_token=${encodeURIComponent(nextPageToken)}`;
        }
        
        console.info(`GOOGLE JOBS API: Searching for jobs with query "${query}"${location ? ` in ${location}` : ''}`);
        
        const response = await fetch(searchUrl);
        const data = await response.json();
        
        if (!response.ok) {
            console.error(`Google Jobs API error: ${data.error || response.statusText}`);
            return { jobs: [], hasMore: false };
        }
        
        // Check if we have job results
        if (!data.jobs || data.jobs.length === 0) {
            console.info(`No job results found for "${query}"`);
            return { jobs: [], hasMore: false };
        }
        
        // Log the number of jobs found
        console.info(`Found ${data.jobs.length} job listings for "${query}"`);
        
        // Process the jobs to extract relevant information
        const processedJobs = data.jobs.map(job => ({
            title: job.title || 'Unknown Title',
            company: job.company_name || 'Unknown Company',
            location: job.location || 'Unknown Location',
            posted_at: job.detected_extensions?.posted_at || 'Unknown',
            schedule: job.detected_extensions?.schedule || 'Unknown',
            description: job.description || 'No description available',
            highlights: job.job_highlights || [],
            extensions: job.extensions || [],
            apply_link: job.apply_link || null,
            apply_links: job.apply_links || [],
            source: job.via ? job.via.replace('via ', '') : 'Unknown Source'
        }));
        
        return {
            jobs: processedJobs,
            hasMore: !!data.pagination?.next_page_token,
            nextPageToken: data.pagination?.next_page_token || null
        };
        
    } catch (error) {
        console.error(`Error during Google Jobs API call for "${query}": ${error.message}`);
        return { jobs: [], hasMore: false };
    }
}

/**
 * Searches for all job listings across multiple pages
 * @param {string} query - The search query
 * @param {string} location - Optional location filter
 * @param {number} maxPages - Maximum number of pages to fetch (default: 5)
 * @returns {Promise<Array>} - All job listings
 */
async function searchAllJobs(query, location = '', maxPages = 5) {
    let allJobs = [];
    let nextPageToken = null;
    let currentPage = 0;
    
    do {
        currentPage++;
        console.info(`Fetching page ${currentPage} of job results...`);
        
        const result = await searchJobs(query, location, nextPageToken);
        
        if (result.jobs.length === 0) {
            break;
        }
        
        allJobs = [...allJobs, ...result.jobs];
        nextPageToken = result.nextPageToken;
        
        // Add a small delay between requests to avoid rate limiting
        if (result.hasMore && currentPage < maxPages) {
            await new Promise(resolve => setTimeout(resolve, 1000));
        }
        
    } while (nextPageToken && currentPage < maxPages);
    
    console.info(`Fetched a total of ${allJobs.length} jobs across ${currentPage} pages`);
    return allJobs;
}

/**
 * Extracts structured data from job listings
 * @param {Array} jobs - Array of job objects from searchJobs or searchAllJobs
 * @returns {Array} - Array of structured job data ready for database insertion
 */
function processJobsForDatabase(jobs) {
    return jobs.map(job => {
        // Extract salary information from description or highlights
        const salaryInfo = extractSalaryInfo(job);
        
        // Extract skills from description or highlights
        const skills = extractSkills(job);
        
        // Calculate experience level based on title and description
        const experienceLevel = calculateExperienceLevel(job);
        
        // Format the job for database insertion
        return {
            title: job.title,
            company: job.company,
            location: job.location,
            posted_at: job.posted_at,
            schedule: job.schedule,
            description: job.description,
            salary_min: salaryInfo.min,
            salary_max: salaryInfo.max,
            salary_currency: salaryInfo.currency,
            salary_period: salaryInfo.period,
            skills: skills,
            experience_level: experienceLevel,
            apply_link: job.apply_link,
            source: job.source,
            scraped_at: new Date().toISOString()
        };
    });
}

/**
 * Extracts salary information from job description and highlights
 * @param {Object} job - Job object
 * @returns {Object} - Structured salary information
 */
function extractSalaryInfo(job) {
    const salaryInfo = {
        min: null,
        max: null,
        currency: 'USD',
        period: 'yearly'
    };
    
    // Check job highlights first
    if (job.highlights && job.highlights.length > 0) {
        for (const highlight of job.highlights) {
            if (highlight.title === 'Compensation' && highlight.items && highlight.items.length > 0) {
                for (const item of highlight.items) {
                    const salaryMatch = item.match(/\$([0-9,.]+)(?:\s*-\s*\$([0-9,.]+))?(?:\s*(per|a|\/)\s*(hour|year|month|week|day))?/i);
                    if (salaryMatch) {
                        salaryInfo.min = parseFloat(salaryMatch[1].replace(/,/g, ''));
                        salaryInfo.max = salaryMatch[2] ? parseFloat(salaryMatch[2].replace(/,/g, '')) : salaryInfo.min;
                        
                        if (salaryMatch[4]) {
                            const period = salaryMatch[4].toLowerCase();
                            if (period === 'hour') salaryInfo.period = 'hourly';
                            else if (period === 'year') salaryInfo.period = 'yearly';
                            else if (period === 'month') salaryInfo.period = 'monthly';
                            else if (period === 'week') salaryInfo.period = 'weekly';
                            else if (period === 'day') salaryInfo.period = 'daily';
                        }
                        
                        break;
                    }
                }
            }
        }
    }
    
    // If no salary found in highlights, check description
    if (!salaryInfo.min && job.description) {
        const salaryMatch = job.description.match(/\$([0-9,.]+)(?:\s*-\s*\$([0-9,.]+))?(?:\s*(per|a|\/)\s*(hour|year|month|week|day))?/i);
        if (salaryMatch) {
            salaryInfo.min = parseFloat(salaryMatch[1].replace(/,/g, ''));
            salaryInfo.max = salaryMatch[2] ? parseFloat(salaryMatch[2].replace(/,/g, '')) : salaryInfo.min;
            
            if (salaryMatch[4]) {
                const period = salaryMatch[4].toLowerCase();
                if (period === 'hour') salaryInfo.period = 'hourly';
                else if (period === 'year') salaryInfo.period = 'yearly';
                else if (period === 'month') salaryInfo.period = 'monthly';
                else if (period === 'week') salaryInfo.period = 'weekly';
                else if (period === 'day') salaryInfo.period = 'daily';
            }
        }
    }
    
    return salaryInfo;
}

/**
 * Extracts skills from job description and highlights
 * @param {Object} job - Job object
 * @returns {Array} - Array of skills
 */
function extractSkills(job) {
    const commonCulinarySkills = [
        'cooking', 'baking', 'grilling', 'sautéing', 'knife skills', 
        'food preparation', 'menu planning', 'recipe development',
        'food safety', 'sanitation', 'inventory management', 'kitchen management',
        'plating', 'garnishing', 'culinary arts', 'pastry', 'butchery',
        'sous vide', 'food presentation', 'catering', 'banquet'
    ];
    
    const skills = [];
    
    // Check if any common culinary skills are mentioned in the description
    if (job.description) {
        for (const skill of commonCulinarySkills) {
            if (job.description.toLowerCase().includes(skill.toLowerCase())) {
                skills.push(skill);
            }
        }
    }
    
    // Check job highlights for skills
    if (job.highlights && job.highlights.length > 0) {
        for (const highlight of job.highlights) {
            if (highlight.title === 'Qualifications' && highlight.items && highlight.items.length > 0) {
                for (const item of highlight.items) {
                    for (const skill of commonCulinarySkills) {
                        if (item.toLowerCase().includes(skill.toLowerCase()) && !skills.includes(skill)) {
                            skills.push(skill);
                        }
                    }
                }
            }
        }
    }
    
    return skills;
}

/**
 * Calculates experience level based on job title and description
 * @param {Object} job - Job object
 * @returns {string} - Experience level (entry, mid, senior, executive)
 */
function calculateExperienceLevel(job) {
    const title = job.title.toLowerCase();
    const description = job.description.toLowerCase();
    
    // Check for executive level positions
    if (title.includes('executive chef') || 
        title.includes('head chef') || 
        title.includes('chef de cuisine') ||
        title.includes('culinary director')) {
        return 'executive';
    }
    
    // Check for senior level positions
    if (title.includes('senior') || 
        title.includes('sr.') || 
        title.includes('lead') ||
        title.includes('sous chef')) {
        return 'senior';
    }
    
    // Check for entry level positions
    if (title.includes('junior') || 
        title.includes('jr.') || 
        title.includes('entry') ||
        title.includes('trainee') ||
        title.includes('apprentice') ||
        title.includes('commis')) {
        return 'entry';
    }
    
    // Default to mid-level
    return 'mid';
}

export {
    searchJobs,
    searchAllJobs,
    processJobsForDatabase
};
