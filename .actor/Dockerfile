# Specify the base Docker image.
FROM apify/actor-node:20
# ARG CACHE_BUST=1 # No longer needed with simpler image?

# Explicitly set user to root before running apk
USER root

# Install PostgreSQL runtime client libraries (using apk for Alpine)
# RUN echo "Cache Bust Value: $CACHE_BUST" && \
RUN apk update && \
    apk add --no-cache postgresql-libs && \
    rm -rf /var/lib/apt/lists/* # This cleanup might not apply to apk, let's remove
    
# Remove apk cache
RUN rm -rf /var/cache/apk/*


# Check preinstalled packages (puppeteer check removed)
RUN npm ls crawlee apify playwright

# Set WORKDIR early
WORKDIR /usr/src/app

# Copy package files
COPY package*.json ./

# Install NPM dependencies (runs as root)
RUN npm --quiet set progress=false \
    && npm install --omit=dev --omit=optional \
    # Check for crawlee remains useful
    && echo "--- Checking for crawlee install ---" \
    && if [ -d "node_modules/crawlee" ]; then echo "FOUND node_modules/crawlee"; else echo "ERROR: node_modules/crawlee NOT FOUND after npm install"; exit 1; fi \
    && echo "--- End check ---" \
    && echo "Installed NPM packages:" \
    && (npm list --omit=dev --all || true) \
    && echo "Node.js version:" \
    && node --version \
    && echo "NPM version:" \
    && npm --version \
    && rm -r ~/.npm

# Copy the rest of the application code
COPY . .

# Create necessary directories
RUN mkdir -p /usr/src/app/src/views \
    && mkdir -p /usr/src/app/src/public \
    && chown -R root:root /usr/src/app # Ensure root owns before switch

# Create and switch to non-root user (Alpine syntax)
RUN adduser -h /home/apify -D apify && \
    chown -R apify:apify /usr/src/app /home/apify
USER apify

# WORKDIR /usr/src/app # Already set

# Run the image (as apify user) - Remove diagnostics for now
CMD npm start --silent
