import json
from itertools import permutations

def main():
    # Adjusted city days to sum to exactly 30 days
    city_days = {
        'Santorini': 4,
        'Krakow': 4,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 4,
        'Geneva': 2,
        'Amsterdam': 3,
        'Budapest': 4,
        'Split': 1
    }
    
    # Verify total days
    assert sum(city_days.values()) == 30, "Total days must be exactly 30"
    
    # Direct flights (undirected graph)
    direct_flights = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Vilnius', 'Munich'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Amsterdam', 'Vilnius'],
        'Vilnius': ['Munich', 'Amsterdam', 'Paris', 'Split', 'Krakow'],
        'Munich': ['Vilnius', 'Split', 'Amsterdam', 'Geneva', 'Krakow', 'Paris', 'Budapest'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Vilnius', 'Krakow', 'Santorini'],
        'Budapest': ['Amsterdam', 'Paris', 'Geneva', 'Munich'],
        'Split': ['Paris', 'Munich', 'Amsterdam', 'Geneva', 'Vilnius', 'Krakow'],
        'Santorini': ['Geneva', 'Amsterdam']
    }
    
    # Constraints
    constraints = {
        'Santorini': (24, 29),  # Days 24-27 (4 days)
        'Krakow': (17, 23),     # Days 17-20 (4 days)
        'Paris': (10, 16)       # Days 10-14 (5 days)
    }
    
    # Fixed segments based on constraints
    fixed_segments = [
        (10, 14, 'Paris'),
        (17, 20, 'Krakow'),
        (24, 27, 'Santorini')
    ]
    
    # Remaining cities and days
    remaining_cities = [city for city in city_days if city not in constraints]
    remaining_days = []
    
    # Days before Paris (1-9)
    remaining_days.append((1, 9))
    
    # Days between Paris and Krakow (15-16)
    remaining_days.append((15, 16))
    
    # Days between Krakow and Santorini (21-23)
    remaining_days.append((21, 23))
    
    # Days after Santorini (28-30)
    remaining_days.append((28, 30))
    
    # Try different permutations of remaining cities
    for perm in permutations(remaining_cities):
        itinerary = fixed_segments.copy()
        current_perm = list(perm)
        
        # Try to place remaining cities in the available slots
        try:
            # Place cities in days 1-9 (6 days needed)
            days_needed = sum(city_days[city] for city in current_perm if city in ['Vilnius', 'Munich', 'Geneva', 'Amsterdam'])
            if days_needed > 9:
                continue
                
            # Place Vilnius (3 days) - needs connection to Paris
            if 'Vilnius' in current_perm:
                # Must be placed before Paris (days 1-9) and connect to Paris
                itinerary.insert(0, (7, 9, 'Vilnius'))  # Days 7-9
                current_perm.remove('Vilnius')
            
            # Place Munich (4 days) - can connect to Paris or Vilnius
            if 'Munich' in current_perm:
                itinerary.insert(0, (3, 6, 'Munich'))  # Days 3-6
                current_perm.remove('Munich')
            
            # Place Amsterdam (3 days) - can connect to Paris
            if 'Amsterdam' in current_perm:
                itinerary.insert(0, (1, 3, 'Amsterdam'))  # Days 1-3
                current_perm.remove('Amsterdam')
            
            # Place remaining cities in other slots
            # Geneva (2 days) - can go after Paris (days 15-16)
            if 'Geneva' in current_perm:
                itinerary.append((15, 16, 'Geneva'))
                current_perm.remove('Geneva')
            
            # Budapest (4 days) - can go after Krakow (days 21-24 but overlaps Santorini)
            # Alternative: place before Paris if possible
            if 'Budapest' in current_perm:
                # Try to place before Paris
                if 5 <= (9 - city_days['Budapest']):
                    start_day = 5
                    itinerary.insert(0, (start_day, start_day + city_days['Budapest'] - 1, 'Budapest'))
                    current_perm.remove('Budapest')
            
            # Split (1 day) - flexible
            if 'Split' in current_perm:
                # Place on day 21
                itinerary.append((21, 21, 'Split'))
                current_perm.remove('Split')
            
            # Verify all cities are placed
            if current_perm:
                continue
                
            # Sort itinerary by start day
            itinerary.sort(key=lambda x: x[0])
            
            # Verify flight connections
            valid = True
            for i in range(len(itinerary)-1):
                current_city = itinerary[i][2]
                next_city = itinerary[i+1][2]
                if next_city not in direct_flights[current_city]:
                    valid = False
                    break
            
            if valid:
                # Format the output
                result = {"itinerary": []}
                for start, end, city in itinerary:
                    if start == end:
                        day_range = f"Day {start}"
                    else:
                        day_range = f"Day {start}-{end}"
                    result["itinerary"].append({"day_range": day_range, "place": city})
                
                print(json.dumps(result))
                return
                
        except (ValueError, IndexError):
            continue
    
    print(json.dumps({"error": "No valid itinerary found that satisfies all constraints"}))

if __name__ == "__main__":
    main()