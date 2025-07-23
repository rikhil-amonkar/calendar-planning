import json
from itertools import permutations

def find_valid_itinerary():
    # Define the cities and their required days
    cities = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4
    }
    
    # Define the direct flight connections
    connections = {
        "London": ["Copenhagen", "Mykonos", "Nice", "Oslo"],
        "Copenhagen": ["London", "Tallinn", "Nice", "Oslo"],
        "Tallinn": ["Copenhagen", "Oslo"],
        "Mykonos": ["London", "Nice"],
        "Oslo": ["Tallinn", "Nice", "London", "Copenhagen"],
        "Nice": ["Oslo", "London", "Mykonos", "Copenhagen"]
    }
    
    # Constraints
    total_days = 16
    conference_days = [14, 15, 16]  # Day 14-16 in Nice
    oslo_friend_days = range(10, 15)  # Day 10-14 in Oslo
    
    # Generate all possible permutations of the cities (limit to 6 cities)
    for perm in permutations(cities.keys()):
        # Check if both Nice and Oslo are in the permutation
        if "Nice" not in perm or "Oslo" not in perm:
            continue
            
        # Check if the permutation is a valid path considering flight connections
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in connections[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
        
        # Initialize variables for day assignment
        day = 1
        itinerary = []
        remaining_cities = cities.copy()
        valid = True
        
        # Assign days to each city in the permutation
        for city in perm:
            days_needed = remaining_cities[city]
            
            # Special handling for Nice and Oslo
            if city == "Nice":
                # Nice must cover days 14-16 (3 days)
                start_day = max(14 - (days_needed - 1), day)
                end_day = start_day + days_needed - 1
                if end_day > 16:
                    valid = False
                    break
            elif city == "Oslo":
                # Oslo must overlap with days 10-14 (5 days)
                # Try to position Oslo to cover as much of 10-14 as possible
                if day <= 10:
                    start_day = 10
                elif day <= 14 - (days_needed - 1):
                    start_day = day
                else:
                    start_day = max(14 - (days_needed - 1), day)
                end_day = start_day + days_needed - 1
                
                # Check if this covers at least some of 10-14
                if end_day < 10 or start_day > 14:
                    valid = False
                    break
            else:
                # For other cities, assign consecutive days starting from current day
                start_day = day
                end_day = start_day + days_needed - 1
            
            # Check if this assignment exceeds total days
            if end_day > total_days:
                valid = False
                break
                
            # Add to itinerary
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            
            # Update current day and mark city as assigned
            day = end_day + 1
            remaining_cities[city] = 0
        
        # Check if all cities were assigned and all constraints met
        if valid and day <= total_days + 1 and all(v == 0 for v in remaining_cities.values()):
            # Verify Nice and Oslo constraints
            nice_ok = False
            oslo_ok = False
            for item in itinerary:
                if item["place"] == "Nice":
                    start, end = map(int, item["day_range"].split(" ")[1].split("-"))
                    if start <= 14 and end >= 16:
                        nice_ok = True
                if item["place"] == "Oslo":
                    start, end = map(int, item["day_range"].split(" ")[1].split("-"))
                    if start <= 14 and end >= 10:
                        oslo_ok = True
            
            if nice_ok and oslo_ok:
                return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute the function and print the result
result = find_valid_itinerary()
print(json.dumps(result, indent=2))