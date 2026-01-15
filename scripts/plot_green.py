
import numpy as np
import matplotlib.pyplot as plt

def green_function(c, z, max_iter=100, R=2.0):
    """
    Compute Green's function G_c(z) using the escape time algorithm.
    G_c(z) = lim 1/2^n * log|f_c^n(z)|
    """
    g = np.zeros_like(z, dtype=float)
    escaped = np.zeros_like(z, dtype=bool)
    
    zn = z.copy()
    
    # We need a large escape radius for better approximation of Green's function
    # R should be at least max(2, |c|)
    escape_radius = max(R, abs(c) + 0.1) if abs(c) > 0 else 2.0
    if abs(c) > 2:
         escape_radius = abs(c)
    
    # Iterate
    for n in range(max_iter):
        mask = (~escaped) & (np.abs(zn) > escape_radius)
        if np.any(mask):
            # For points that just escaped:
            # G(z) approx 1/2^n * log|zn|
            g[mask] = (1.0 / (2**n)) * np.log(np.abs(zn[mask]))
            escaped[mask] = True
        
        # Don't iterate escaped points to avoid overflow
        not_escaped = ~escaped
        zn[not_escaped] = zn[not_escaped]**2 + c
        
    # For points that didn't escape (inside Julia set), G(z) = 0
    # But we might have points that escape later or are very close.
    # We can refine the escaped ones.
    
    # Correct the potential for escaped points
    # The loop above sets g when they CROSS the boundary.
    # But strictly speaking we want the limit.
    # 1/2^n log|z_n| is constant for large n for the exact map f(z)=z^2.
    # For f_c(z) ~ z^2 at infinity, this holds.
    
    return g

def plot_green(c, ax, title):
    # Grid
    x = np.linspace(-2.0, 2.0, 400)
    y = np.linspace(-1.5, 1.5, 300)
    X, Y = np.meshgrid(x, y)
    Z = X + 1j * Y
    
    G = green_function(c, Z, max_iter=50)
    
    # Plot contours
    # Levels: non-linear spacing to show details near the set
    levels = [0, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0]
    
    # Heatmap
    im = ax.imshow(G, extent=[-2, 2, -1.5, 1.5], origin='lower', cmap='viridis', vmax=1.5)
    
    # Contours
    ax.contour(X, Y, G, levels=levels, colors='white', linewidths=0.5)
    
    # Filled Julia set approximation (where G is close to 0)
    ax.contourf(X, Y, G, levels=[0, 0.01], colors='black')
    
    ax.set_title(title)
    ax.set_xlabel('Re(z)')
    ax.set_ylabel('Im(z)')

def main():
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    
    # Case 1: c = 0 (Circle)
    plot_green(0, axes[0], "c = 0 (Unit Disk)")
    
    # Case 2: c = -1 (Basilica)
    plot_green(-1, axes[1], "c = -1 (Basilica)")
    
    plt.tight_layout()
    plt.savefig('../docs/images/green_function_plots.png', dpi=300)
    print("Saved ../docs/images/green_function_plots.png")

if __name__ == "__main__":
    main()
