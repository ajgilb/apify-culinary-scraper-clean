/**
 * Uses SearchAPI.io to find the website URL for a company name.
 */
async function getWebsiteUrlFromSearchAPI(companyName) {
    const apiKey = process.env.SEARCH_API_KEY;

    if (!apiKey) {
        console.warn('SEARCH_API_KEY environment variable not found. Skipping search.');
        return null;
    }

    if (!companyName || companyName === 'Unknown' || companyName.startsWith('Excluded:')) {
        console.info(`Skipping search for invalid/excluded company: ${companyName}`);
        return null;
    }

    try {
        // Create search query - add "official website" to improve results
        const searchQuery = `${companyName} official website`;

        // Build the API URL
        const searchUrl = `https://www.searchapi.io/api/v1/search?engine=google&q=${encodeURIComponent(searchQuery)}&api_key=${apiKey}`;

        console.info(`SEARCH API: Searching for "${searchQuery}"`);

        const response = await fetch(searchUrl);
        const data = await response.json();

        if (!response.ok) {
            console.error(`Search API error: ${data.error || response.statusText}`);
            return null;
        }

        // Check if we have organic results
        if (!data.organic_results || data.organic_results.length === 0) {
            console.info(`No search results found for "${companyName}"`);
            return null;
        }

        // Log all results for debugging
        console.info(`Found ${data.organic_results.length} search results for "${companyName}"`);
        data.organic_results.slice(0, 3).forEach((result, index) => {
            console.info(`Result #${index+1}: ${result.title} - ${result.link} (${result.domain})`);
        });

        // Simply use the first result from SearchAPI.io
        // SearchAPI.io already ranks results by relevance, so the first result is usually the best match
        const firstResult = data.organic_results[0];

        // Just do a basic check to avoid social media sites
        const nonCompanySites = ['linkedin.com', 'facebook.com', 'instagram.com', 'twitter.com', 'indeed.com', 'glassdoor.com', 'yelp.com'];
        if (nonCompanySites.some(site => firstResult.domain.includes(site))) {
            console.info(`First result is a social media site, checking second result...`);

            // If there's a second result, use that instead
            if (data.organic_results.length > 1) {
                const secondResult = data.organic_results[1];
                if (!nonCompanySites.some(site => secondResult.domain.includes(site))) {
                    console.info(`Using second result: ${secondResult.link}`);
                    return secondResult.link;
                }
            }

            console.info(`No good alternative found for "${companyName}"`);
            return null;
        }

        console.info(`Using first result: ${firstResult.link}`);
        return firstResult.link;

    } catch (error) {
        console.error(`Error during Search API call for "${companyName}": ${error.message}`);
        return null;
    }
}

export default getWebsiteUrlFromSearchAPI;
