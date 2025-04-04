# Specify the base Docker image. You can read more about
# the available images at https://docs.apify.com/sdk/js/docs/guides/docker-images
# You can also use any other image from Docker Hub.
FROM apify/actor-node:20

# Check preinstalled packages
RUN npm ls crawlee apify puppeteer playwright

# Copy just package.json and package-lock.json
COPY package*.json ./

# Install NPM packages
RUN npm --quiet set progress=false \
    && npm install --omit=dev --omit=optional \
    && echo "Installed NPM packages:" \
    && (npm list --omit=dev --all || true) \
    && echo "Node.js version:" \
    && node --version \
    && echo "NPM version:" \
    && npm --version \
    && rm -r ~/.npm

# Copy the source code
COPY . /usr/src/app/

# Create necessary directories
RUN mkdir -p /usr/src/app/src/views \
    && mkdir -p /usr/src/app/src/public

# Create and run as non-root user
RUN adduser -h /home/apify -D apify && \
    chown -R apify:apify /usr/src/app
USER apify

WORKDIR /usr/src/app

# Run the image
CMD npm start --silent
