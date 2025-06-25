import itertools
import json

def main():
    # Define the cities and their durations
    cities = ["Vienna", "Lyon", "Santorini", "Amsterdam"]
    durations = {
        "Vienna": 7,
        "Lyon": 3,
        "Santorini": 4,
        "Amsterdam": 3
    }
    
    # Event constraints: (start_day, end_day) inclusive
    events = {
        "Lyon": (7, 9),
        "Amsterdam": (9, 11)
    }
    
    # Direct flight graph (undirected)
    graph = {
        ("Vienna", "Lyon"),
        ("Vienna", "Santorini"),
        ("Vienna", "Amsterdam"),
        ("Amsterdam", "Santorini"),
        ("Lyon", "Amsterdam")
    }
    
    # Helper function to check flight connectivity
    def connected(c1, c2):
        return (c1, c2) in graph or (c2, c1) in graph
    
    # Helper function to check interval overlap
    def intervals_overlap(interval1, interval2):
        a1, a2 = interval1
        b1, b2 = interval2
        return max(a1, b1) <= min(a2, b2)
    
    # Generate all permutations of the cities
    perms = itertools.permutations(cities)
    solution = None
    
    for perm in perms:
        # Check flight connections between consecutive cities
        if not connected(perm[0], perm[1]):
            continue
        if not connected(perm[1], perm[2]):
            continue
        if not connected(perm[2], perm[3]):
            continue
        
        # Calculate block boundaries
        d = [durations[city] for city in perm]
        e1 = d[0]  # end of first city block
        e2 = e1 + d[1] - 1  # end of second city block
        e3 = e2 + d[2] - 1  # end of third city block
        
        # Define blocks for each city in the permutation
        blocks = [
            (1, e1),        # Block for first city
            (e1, e2),       # Block for second city
            (e2, e3),       # Block for third city
            (e3, 14)        # Block for fourth city
        ]
        
        # Find indices for Lyon and Amsterdam
        lyon_index = perm.index("Lyon")
        amsterdam_index = perm.index("Amsterdam")
        
        # Check if Lyon and Amsterdam blocks satisfy event constraints
        lyon_block = blocks[lyon_index]
        amsterdam_block = blocks[amsterdam_index]
        
        if not intervals_overlap(lyon_block, events["Lyon"]):
            continue
        if not intervals_overlap(amsterdam_block, events["Amsterdam"]):
            continue
        
        # Build itinerary for this permutation
        itinerary = []
        for i in range(4):
            start, end = blocks[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({
                "day_range": day_range_str,
                "place": perm[i]
            })
        
        solution = itinerary
        break  # Found a valid solution
    
    # Output the result as JSON
    if solution is None:
        # Fallback: return empty itinerary if no solution found (though we expect one)
        result = {"itinerary": []}
    else:
        result = {"itinerary": solution}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()