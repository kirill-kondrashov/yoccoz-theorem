
import numpy as np
import matplotlib.pyplot as plt

def iterate_potential(c, z0, max_n=15):
    """
    Computes the sequence G_n(z) = 1/2^n * log(max(1, |z_n|))
    Returns arrays of n and G_n.
    """
    ns = np.arange(max_n + 1)
    g_ns = []
    
    z = z0
    for n in range(max_n + 1):
        # Calculate potential at step n
        try:
            val = np.abs(z)
        except OverflowError:
            val = float('inf')
            
        pot = 0.0
        if val == float('inf'):
            # If we overflowed, the potential has stabilized to machine precision
            # We just repeat the last value
            if len(g_ns) > 0:
                pot = g_ns[-1]
            else:
                 pot = 0 # Should not happen for escaping points
        elif val > 1.0:
            pot = np.log(val) / (2**n)
            
        g_ns.append(pot)
        
        # Next iterate
        # Stop iterating if we are already huge to prevent overflow exception
        if val < 1e100:
             z = z**2 + c
        else:
             z = float('inf') # Mark as infinite for next iter
        
    return ns, np.array(g_ns)

def main():
    c = -1.0 # Basilica
    
    # Define points
    points = [
        {"z": 0.0, "label": "Inside K(c) (z=0)", "color": "green", "marker": "o"},
        {"z": 1.62, "label": "Close to Boundary (z=1.62)", "color": "orange", "marker": "s"}, # Golden ratio is ~1.618
        {"z": 3.0, "label": "Far Escaping (z=3.0)", "color": "blue", "marker": "^"}
    ]
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    # Plot 1: The Sequence G_n(z)
    ax1.set_title("Sequence Convergence: $G_n(z)$")
    ax1.set_xlabel("Iteration $n$")
    ax1.set_ylabel("Potential $G_n(z)$")
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Convergence Rate |G_{n+1} - G_n|
    ax2.set_title("Cauchy Difference: $|G_{n+1}(z) - G_n(z)|$")
    ax2.set_xlabel("Iteration $n$")
    ax2.set_ylabel("Difference (log scale)")
    ax2.set_yscale('log')
    ax2.grid(True, alpha=0.3)
    
    for p in points:
        ns, g_ns = iterate_potential(c, p["z"])
        
        # Plot sequence
        ax1.plot(ns, g_ns, label=p["label"], color=p["color"], marker=p["marker"], markersize=4, alpha=0.8)
        
        # Plot differences (stop one early)
        diffs = np.abs(np.diff(g_ns))
        # Filter out zeros for log plot
        valid_indices = diffs > 1e-15
        if np.any(valid_indices):
             ax2.plot(ns[:-1][valid_indices], diffs[valid_indices], 
                      label=p["label"], color=p["color"], marker=p["marker"], markersize=4, linestyle='--')
    
    ax1.legend()
    ax2.legend()
    
    plt.tight_layout()
    plt.savefig('../docs/images/convergence_plots.png', dpi=300)
    print("Saved ../docs/images/convergence_plots.png")

if __name__ == "__main__":
    main()
