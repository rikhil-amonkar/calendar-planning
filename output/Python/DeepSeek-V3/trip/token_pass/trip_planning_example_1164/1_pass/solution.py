import json

def solve():
    # Cities and required days
    cities = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2
    }
    
    # Fixed constraints: (city, start_day, end_day) inclusive
    constraints = [
        ("Reykjavik", 3, 4),
        ("Stockholm", 4, 5),
        ("Porto", 13, 17),
        ("Vienna", 11, 13)
    ]
    
    # Direct flights (undirected)
    direct_flights = [
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Porto"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Vienna", "Porto")
    ]
    
    # Make flight lookup set
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    # Day count
    total_days = 17
    
    # We'll store assignments as list of cities for each day 1..17
    assignment = [None] * total_days  # index 0 = day 1
    
    # Track remaining days per city
    remaining = cities.copy()
    
    # Apply fixed constraints first
    for city, start, end in constraints:
        for d in range(start - 1, end):  # convert to 0-based index
            assignment[d] = city
            remaining[city] -= 1
            if remaining[city] < 0:
                return None  # impossible
    
    # Helper to check if two cities are connected
    def can_fly(a, b):
        return (a, b) in flight_set
    
    # Backtracking search
    def backtrack(day):
        if day == total_days:
            # All days assigned, check all cities have 0 remaining days
            return all(v == 0 for v in remaining.values())
        
        # If already assigned by constraint, move to next day
        if assignment[day] is not None:
            return backtrack(day + 1)
        
        # Try each city
        for city in cities:
            if remaining[city] <= 0:
                continue
            
            # Check flight constraint from previous day
            if day > 0 and assignment[day - 1] is not None:
                prev_city = assignment[day - 1]
                if prev_city != city and not can_fly(prev_city, city):
                    continue
            
            # Assign
            assignment[day] = city
            remaining[city] -= 1
            
            if backtrack(day + 1):
                return True
            
            # Undo
            assignment[day] = None
            remaining[city] += 1
        
        return False
    
    if not backtrack(0):
        return {"error": "No valid itinerary found"}
    
    # Convert assignment to itinerary format with day ranges
    itinerary = []
    current_city = assignment[0]
    start_day = 1
    for i in range(1, total_days):
        if assignment[i] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{i}",
                "place": current_city
            })
            current_city = assignment[i]
            start_day = i + 1
    # Add last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": current_city
    })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))