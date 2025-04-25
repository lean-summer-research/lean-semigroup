      
# Project Setup

This project includes a Development Container (Dev Container) configuration to ensure all we all use a consistent Lean 4 toolchain version. This prevents environment-related issues.

You can work on this project in three ways:

1.  **Standard Local Development:** Clone the repository and use your existing local VS Code and Lean 4 installation. This requires you to manually ensure your Lean and `mathlib` versions match the project's requirements (`lean-toolchain` file).
2.  **GitHub Codespaces:** Use the Dev Container running on GitHub's infrastructure via a web-based or locally connected VS Code.
3.  **Local Dev Container:** Use the Dev Container running locally on your machine via Docker Desktop and a VS Code extension.

Options 2 and 3 use the Dev Container defined in the `.devcontainer` folder, providing a pre-configured environment.

## Understanding Dev Containers

The `.devcontainer` folder contains configuration files (`devcontainer.json` and a `Dockerfile`) that define a specific development environment inside a Docker container.

*   **Docker Container:** An isolated, lightweight virtual environment. It packages the necessary operating system (Ubuntu, in this case), system dependencies, the `elan` version manager, the lean4 VS Code extension, and fetches the `mathlib` cache.
*   **Build Process:** When you first launch the Dev Container (either via Codespaces or locally), Docker builds this environment based on the `Dockerfile` and `devcontainer.json`. This initial build can take **5-10 minutes** as it downloads the base system, installs tools, and prepares the `mathlib` cache.
*   **Faster Startup:** After the initial build, the container image is stored. Subsequent launches will reuse this image, making startup much faster as only the project files need to be loaded into the already-built environment.

You can interact with this containerized environment using either GitHub Codespaces or a local VS Code setup with specific prerequisites.


## Option 1: Standard Local Development

If you don't want to deal with any of this dev container stuff, you can clone the repository and open it in your local VS Code instance.


## Option 2: GitHub Codespaces

This method runs the Dev Container on GitHub's servers, accessible via a web browser or your local VS Code instance. No local Docker installation is required. I recommend trying this out first becuse its basically a one-click setup for getting the entire environment and project loaded at once (even the vscode extention and mathlib cache).

### Usage:

Navigate to the repository page on GitHub: https://github.com/lean-summer-research/lean-semigroup

Click the green <> Code button.

Select the "Codespaces" tab and create a new codespace. In the future, you will be able to enter into an already built codespace from this menu.

Wait for the initial build (5-10 minutes).

The Codespace will open in your browser with a VS Code interface, containing the project files and the pre-configured Lean 4 environment.

(Optional Connection): To use your local VS Code interface, click the green remote indicator button in the bottom-left corner of VS Code and select "Connect to Codespace...".

Edit files and use the integrated terminal or Source Control panel for Git operations (pull, add, commit, push). Changes are pushed directly to the GitHub repository.

Note: Requires an internet connection. Performance is fine but the next option is probably faster.

## Option 3: Local Dev Container via VS Code Extension

This method runs the Dev Container directly on your machine using Docker Desktop and the VS Code Dev Containers extension. This often provides slightly better performance as it uses local resources.

### Dependencies:

Install Docker Desktop: Download from docker.com, install, and ensure it is running before proceeding. The VS Code extension depends on it.

Install VS Code Extension: Open VS Code, navigate to the Extensions view, search for Dev Containers (by Microsoft), and install it.

### Usage:

Clone the repository locally if you haven't already.

Open the repository folder in VS Code (`code .`).

VS Code should detect the .devcontainer configuration and prompt to "Reopen in Container". Click this button.

If the prompt does not appear, open the Command Palette (Cmd + Shift + P or Ctrl + Shift + P), type Dev Containers: Reopen in Container, and select it.

Wait for the initial build, then VS Code will reload, connecting to the container. The bottom-left status bar will indicate you are in the Dev Container context. 

Edit files and use the integrated terminal or Source Control panel for Git operations (pull, add, commit, push).
