
import numpy as np
import matplotlib.pyplot as plt

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

def plot_view(c, ax, extent, title, zoom_rect=None, is_global=False):
    # Higher resolution
    x = np.linspace(extent[0], extent[1], 800)
    y = np.linspace(extent[2], extent[3], 600)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    # Compute Green's function
    G = green_function(c, Z, max_iter=100)
    
    # Plot background potential (Greys)
    # We want to clearly see the "Basin of Infinity" potential
    ax.imshow(G, extent=extent, origin='lower', cmap='bone_r', vmax=2.0, alpha=0.4)
    
    # Plot filled Julia set (approx G=0)
    ax.contourf(X, Y, G, levels=[0, 0.01], colors=['black'])
    
    # Plot Critical Point and Critical Value
    if is_global:
        ax.plot(0, 0, 'ro', label='Critical Point $0$')
        ax.plot(-1, 0, 'bo', label='Critical Value $-1$')
        ax.legend(loc='upper right', fontsize=8)
    else:
        ax.plot(0, 0, 'ro')
        
    # Contours
    # We want to show how the "Puzzle Piece" cuts off.
    # Level 0 (P_0): G = 1.0 (Outer boundary)
    # Level 1 (P_1): G = 0.5 (Separates components?)
    # For Basilica, 0 and -1 are in different main components if we cut deep enough.
    # Actually, for c=-1, 0 and -1 are in the immediate basin of the superattracting cycle 0 <-> -1.
    # The Julia set touches at the alpha fixed point.
    
    # Let's plot levels: 1.0, 0.5, 0.25, 0.125
    levels = sorted([1.0, 0.5, 0.25, 0.125])
    colors = ['orange', 'green', 'blue', 'purple'] # Match reversed order: 0.125 (orange), 0.25 (green), 0.5 (blue), 1.0 (purple)
    
    cs = ax.contour(X, Y, G, levels=levels, colors=colors, linewidths=1.0)
    ax.clabel(cs, inline=True, fontsize=8, fmt='%.3f')
    
    if zoom_rect:
        from matplotlib.patches import Rectangle
        # zoom_rect is (x, y, w, h)
        rect = Rectangle((zoom_rect[0], zoom_rect[2]), 
                         zoom_rect[1]-zoom_rect[0], 
                         zoom_rect[3]-zoom_rect[2], 
                         linewidth=2, edgecolor='red', facecolor='none', linestyle='-')
        ax.add_patch(rect)
        
        # Draw lines connecting box to the other axes? 
        # Hard to coordinate between subplots simply, but we can just show the box.
        
    ax.set_title(title)
    ax.set_aspect('equal')
    ax.set_xlim(extent[0], extent[1])
    ax.set_ylim(extent[2], extent[3])

def main():
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Basilica c = -1
    # Global View
    # Show wide enough to see the "figure 8" of Basilica
    global_extent = [-2.0, 2.0, -1.5, 1.5]
    zoom_extent = [-0.8, 0.8, -0.8, 0.8]
    
    plot_view(-1, axes[0], global_extent, 
              "Global Geometry ($c=-1$)\nEquipotentials wrap around $K(c)$", 
              zoom_rect=zoom_extent, is_global=True)
    
    # Zoomed View
    plot_view(-1, axes[1], zoom_extent, 
              "Dynamical Puzzle Pieces $P_n(0)$\nNested regions around $0$ defined by $G < 2^{-n}$",
              is_global=False)
              
    # Add an arrow indicating zoom
    # This is tricky in coords, but we can do figure-relative coords
    # Let's just trust the red box.
    
    plt.tight_layout()
    plt.savefig('../docs/images/puzzle_pieces.png', dpi=300)
    print("Saved ../docs/images/puzzle_pieces.png")

if __name__ == "__main__":
    main()
