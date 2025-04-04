import { createPuppeteerRouter } from 'crawlee';

export const router = createPuppeteerRouter();

router.addDefaultHandler(async ({ page, request, log }) => {
    const { username, password } = request.userData || {};

    log.info('Starting scraper on Culinary Agents...');

    // Step 1: Click the login button to open the modal
    log.info('Clicking login button...');
    await page.click("a[href='#signin-modal']");
    
    // Step 2: Wait for the email input field to appear
    await page.waitForSelector('#user_email', { visible: true });
    log.info('Login modal is visible.');

    // Step 3: Enter login credentials
    log.info('Entering email...');
    await page.type('#user_email', username);
    log.info('Entering password...');
    await page.type('#user_password', password);

    // Step 4: Click the login button and wait for navigation
    log.info('Clicking sign in button...');
    await Promise.all([
        page.click("button.btn-primary[type='submit']"),
        page.waitForNavigation({ waitUntil: 'networkidle2' })
    ]);

    log.info('Login successful!');
    
    // Navigate to jobs page
    log.info('Successfully logged in! Navigating to Jobs page...');
    await page.goto('https://culinaryagents.com/jobs', { waitUntil: 'domcontentloaded' });
    
    log.info('On Jobs page, starting data collection...');
    // Continue with the scraping process - let main.js handle the actual data collection
});