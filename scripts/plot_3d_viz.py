
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

def plot_3d_surface(c, filename, title, levels_to_show=None, mode='smooth'):
    # Setup grid - higher resolution for sharp steps
    x = np.linspace(-1.8, 1.8, 400)
    y = np.linspace(-1.3, 1.3, 400)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    # Compute Green's function
    G = green_function(c, Z, max_iter=80)
    
    if mode == 'stepped':
        # Create "Stepped" potential to visualize the puzzle levels
        # instead of smooth potential, we terrace it.
        G_plot = G.copy()
        
        # Create a nice stepped look
        max_steps = 5
        for n in range(max_steps):
            upper = 1.0 / (2**n)
            lower = 1.0 / (2**(n+1))
            mask = (G <= upper) & (G > lower)
            G_plot[mask] = upper
            
        # For G > 1, keep smooth or cap
        G_plot[G > 1.0] = G[G > 1.0]
        # For deep inside, set to 0
        G_plot[G <= 1.0 / (2**max_steps)] = 0.0
        
        cmap_style = 'viridis'
        alpha_val = 0.95
    else:
        # Smooth mode
        G_plot = G
        cmap_style = 'coolwarm'
        alpha_val = 0.8
    
    # Cap for plot visibility
    G_capped = np.minimum(G_plot, 1.5)
    
    fig = plt.figure(figsize=(10, 8))
    ax = fig.add_subplot(111, projection='3d')
    
    # Surface plot
    surf = ax.plot_surface(X, Y, G_capped, cmap=cmap_style, edgecolor='none', alpha=alpha_val, antialiased=True)
    
    # Contours on the surface
    if levels_to_show:
        for level in levels_to_show:
            # Plot contour at the height of the step/level
            ax.contour(X, Y, G, levels=[level], colors='white', linewidths=1.5, zdir='z', offset=level)

    ax.set_title(title)
    ax.set_xlabel('Re(z)')
    ax.set_ylabel('Im(z)')
    ax.set_zlabel('Potential G(z)')
    ax.set_zlim(0, 1.5)
    
    # View angle
    ax.view_init(elev=55, azim=-60)
    
    plt.tight_layout()
    plt.savefig(filename, dpi=300)
    print(f"Saved {filename}")

def main():
    # Basilica c = -1
    levels = [1.0, 0.5, 0.25, 0.125]
    
    # Plot for Puzzle: Smooth potential showing the continuous function and level sets
    plot_3d_surface(-1, '../docs/images/puzzle_3d.png', 
                    "3D Green's Function Potential ($c=-1$)\nSmooth potential with levels $1/2^n$", 
                    levels_to_show=levels, mode='smooth')
    
    # Plot for Yoccoz: Stepped/Terraced view to emphasize the annuli A_n
    plot_3d_surface(-1, '../docs/images/yoccoz_3d.png', 
                    "Discrete Potential Landscape ($c=-1$)\nTerraces correspond to Puzzle Annuli $A_n$", 
                    levels_to_show=levels, mode='stepped')

if __name__ == "__main__":
    main()
