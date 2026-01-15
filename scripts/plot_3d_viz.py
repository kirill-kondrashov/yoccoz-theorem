
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

def green_function(c, z, max_iter=100, R=2.0):
    g = np.zeros_like(z, dtype=float)
    escaped = np.zeros_like(z, dtype=bool)
    zn = z.copy()
    escape_radius = max(R, abs(c) + 0.1) if abs(c) > 0 else 2.0
    if abs(c) > 2: escape_radius = abs(c)
    
    for n in range(max_iter):
        mask = (~escaped) & (np.abs(zn) > escape_radius)
        if np.any(mask):
            g[mask] = (1.0 / (2**n)) * np.log(np.abs(zn[mask]))
            escaped[mask] = True
        not_escaped = ~escaped
        zn[not_escaped] = zn[not_escaped]**2 + c
    return g

def plot_3d_surface(c, filename, title, levels_to_show=None):
    # Setup grid
    x = np.linspace(-1.8, 1.8, 200)
    y = np.linspace(-1.3, 1.3, 200)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    # Compute Green's function
    G = green_function(c, Z, max_iter=80)
    
    # Cap the height for better visualization of the "floor"
    # G goes to infinity, but we care about the structure near K(c)
    G_capped = np.minimum(G, 1.5)
    
    fig = plt.figure(figsize=(10, 8))
    ax = fig.add_subplot(111, projection='3d')
    
    # Surface plot
    # cmap 'viridis' or 'coolwarm'
    surf = ax.plot_surface(X, Y, G_capped, cmap='viridis', edgecolor='none', alpha=0.9)
    
    # Contours on the surface (or slightly above to be visible)
    if levels_to_show:
        for level in levels_to_show:
            ax.contour(X, Y, G, levels=[level], colors='white', linewidths=2.0, zdir='z', offset=level)
            # Also project to bottom?
            # ax.contour(X, Y, G, levels=[level], colors='black', linestyles='dashed', linewidths=1.0, zdir='z', offset=0)

    # Plot filled Julia set at z=0 (approx)
    # ax.contourf(X, Y, G, levels=[0, 0.01], zdir='z', offset=0, colors='black')

    ax.set_title(title)
    ax.set_xlabel('Re(z)')
    ax.set_ylabel('Im(z)')
    ax.set_zlabel('Potential G(z)')
    ax.set_zlim(0, 1.5)
    
    # View angle
    ax.view_init(elev=45, azim=-60)
    
    plt.tight_layout()
    plt.savefig(filename, dpi=300)
    print(f"Saved {filename}")

def main():
    # Basilica c = -1
    levels = [1.0, 0.5, 0.25, 0.125]
    
    # Plot for Puzzle: Focus on levels
    plot_3d_surface(-1, '../docs/images/puzzle_3d.png', 
                    "3D Green's Function Potential ($c=-1$)\nWhite lines: Puzzle Levels $1/2^n$", 
                    levels_to_show=levels)
    
    # Plot for Yoccoz: Maybe same but different title emphasizing the geometry
    # Actually, let's use the same visualization style but tailored caption in LaTeX
    plot_3d_surface(-1, '../docs/images/yoccoz_3d.png', 
                    "Potential Landscape ($c=-1$)\nRecurrent geometry of the levels", 
                    levels_to_show=levels)

if __name__ == "__main__":
    main()
