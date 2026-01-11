import json
from itertools import permutations

def solve_itinerary():
    # City durations
    durations = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Berlin': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Paris', 'Stockholm'),
        ('Seville', 'Paris'),
        ('Naples', 'Zurich'),
        ('Nice', 'Riga'),
        ('Berlin', 'Milan'),
        ('Paris', 'Zurich'),
        ('Paris', 'Nice'),
        ('Milan', 'Paris'),
        ('Milan', 'Riga'),
        ('Paris', 'Lyon'),
        ('Milan', 'Naples'),
        ('Paris', 'Riga'),
        ('Berlin', 'Stockholm'),
        ('Stockholm', 'Riga'),
        ('Nice', 'Zurich'),
        ('Milan', 'Zurich'),
        ('Lyon', 'Nice'),
        ('Zurich', 'Stockholm'),
        ('Zurich', 'Riga'),
        ('Berlin', 'Naples'),
        ('Milan', 'Stockholm'),
        ('Berlin', 'Zurich'),
        ('Milan', 'Seville'),
        ('Paris', 'Naples'),
        ('Berlin', 'Riga'),
        ('Nice', 'Stockholm'),
        ('Berlin', 'Paris'),
        ('Nice', 'Naples'),
        ('Berlin', 'Nice')
    ]
    
    # Convert to adjacency list for easier checking
    flights = {}
    for city1, city2 in direct_flights:
        flights.setdefault(city1, set()).add(city2)
        flights.setdefault(city2, set()).add(city1)
    
    # Fixed constraints: (city, start_day, end_day)
    fixed = [
        ('Berlin', 1, 2),      # Wedding days 1-2
        ('Stockholm', 20, 22), # Show days 20-22
        ('Nice', 12, 13)       # Workshop days 12-13
    ]
    
    # All cities to visit
    all_cities = list(durations.keys())
    
    # Create a timeline of 23 days
    timeline = [None] * 23  # Index 0 = Day 1, Index 22 = Day 23
    
    # Place fixed constraints
    for city, start, end in fixed:
        for day in range(start - 1, end):  # Convert to 0-based index
            timeline[day] = city
    
    # Helper function to check if we can place a city in a range
    def can_place(city, start_day, duration):
        # Check if all days in range are either empty or already this city
        for day in range(start_day, start_day + duration):
            if day >= 23:
                return False
            if timeline[day] is not None and timeline[day] != city:
                return False
        return True
    
    # Helper to place a city
    def place_city(city, start_day, duration):
        for day in range(start_day, start_day + duration):
            timeline[day] = city
    
    # Helper to remove a city from a range
    def remove_city(city, start_day, duration):
        for day in range(start_day, start_day + duration):
            if timeline[day] == city:
                timeline[day] = None
    
    # Backtracking search
    def backtrack(remaining_cities, current_day):
        # If we've filled all days
        if current_day >= 23:
            # Check if all cities are placed with correct durations
            city_counts = {}
            for city in timeline:
                if city:
                    city_counts[city] = city_counts.get(city, 0) + 1
            
            for city, needed in durations.items():
                if city_counts.get(city, 0) != needed:
                    return False
            return True
        
        # If this day is already filled, move to next
        if timeline[current_day] is not None:
            # Skip to next empty day or end
            next_day = current_day
            while next_day < 23 and timeline[next_day] is not None:
                next_day += 1
            return backtrack(remaining_cities, next_day)
        
        # Try to place each remaining city starting at current_day
        for city in list(remaining_cities):
            duration = durations[city]
            
            # Check if we can place it here
            if can_place(city, current_day, duration):
                # Check flight constraint with previous city
                if current_day > 0 and timeline[current_day - 1] is not None:
                    prev_city = timeline[current_day - 1]
                    if prev_city != city:  # Different city means flight needed
                        if city not in flights.get(prev_city, set()):
                            continue  # No direct flight
                
                place_city(city, current_day, duration)
                new_remaining = remaining_cities.copy()
                new_remaining.remove(city)
                
                # Move to next empty spot
                next_day = current_day + duration
                while next_day < 23 and timeline[next_day] is not None:
                    next_day += 1
                
                if backtrack(new_remaining, next_day):
                    return True
                
                # Backtrack
                remove_city(city, current_day, duration)
        
        return False
    
    # Start with all cities except the fixed ones (they're already partially placed)
    remaining = set(all_cities) - {'Berlin', 'Stockholm', 'Nice'}
    
    # Try starting from day 1
    if backtrack(remaining, 0):
        # Convert timeline to itinerary format
        itinerary = []
        current_city = timeline[0]
        start_day = 0
        
        for day in range(1, 23):
            if timeline[day] != current_city:
                # Add previous segment
                if start_day == day - 1:
                    day_range = f"Day {start_day + 1}"
                else:
                    day_range = f"Day {start_day + 1}-{day}"
                itinerary.append({"day_range": day_range, "place": current_city})
                
                current_city = timeline[day]
                start_day = day
        
        # Add last segment
        if start_day == 22:
            day_range = f"Day {start_day + 1}"
        else:
            day_range = f"Day {start_day + 1}-23"
        itinerary.append({"day_range": day_range, "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Main execution
if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))