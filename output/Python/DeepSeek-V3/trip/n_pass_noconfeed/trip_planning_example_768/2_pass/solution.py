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
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities.keys()):
        # Check if the permutation is a valid path considering flight connections
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in connections[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
        
        # Check if both Nice and Oslo are in the permutation
        if "Nice" not in perm or "Oslo" not in perm:
            continue
        
        # Try to assign days to the cities in this permutation
        remaining_cities = cities.copy()
        
        # We'll use a backtracking approach to assign days
        def backtrack(position, current_day, assignments):
            if current_day > total_days + 1:
                return None
                
            if position == len(perm):
                # Check if all cities have been fully assigned
                if all(v == 0 for v in remaining_cities.values()):
                    return assignments
                else:
                    return None
            
            city = perm[position]
            max_days = remaining_cities[city]
            
            # Determine minimum days needed for this city
            min_days = 1 if position < len(perm) - 1 else max_days
            
            for days in range(min_days, max_days + 1):
                if current_day + days - 1 > total_days:
                    continue
                
                # Check constraints for this city
                if city == "Nice":
                    nice_start = current_day
                    nice_end = current_day + days - 1
                    # Nice must cover days 14-16
                    if not (nice_start <= 14 and nice_end >= 16):
                        continue
                
                if city == "Oslo":
                    oslo_start = current_day
                    oslo_end = current_day + days - 1
                    # Oslo must overlap with days 10-14
                    if not (oslo_start <= 14 and oslo_end >= 10):
                        continue
                
                # Make the assignment
                remaining_cities[city] -= days
                new_assignment = {
                    "day_range": f"Day {current_day}-{current_day + days - 1}",
                    "place": city
                }
                
                result = backtrack(position + 1, current_day + days, assignments + [new_assignment])
                if result is not None:
                    return result
                
                # Backtrack
                remaining_cities[city] += days
            
            return None
        
        # Start backtracking
        final_itinerary = backtrack(0, 1, [])
        if final_itinerary is not None:
            # Verify all constraints are met
            nice_assigned = False
            oslo_assigned = False
            for item in final_itinerary:
                if item["place"] == "Nice":
                    start, end = map(int, item["day_range"].split(" ")[1].split("-"))
                    if start <= 14 and end >= 16:
                        nice_assigned = True
                if item["place"] == "Oslo":
                    start, end = map(int, item["day_range"].split(" ")[1].split("-"))
                    if start <= 14 and end >= 10:
                        oslo_assigned = True
            
            if nice_assigned and oslo_assigned:
                return {"itinerary": final_itinerary}
    
    return {"itinerary": []}

# Execute the function and print the result
result = find_valid_itinerary()
print(json.dumps(result, indent=2))