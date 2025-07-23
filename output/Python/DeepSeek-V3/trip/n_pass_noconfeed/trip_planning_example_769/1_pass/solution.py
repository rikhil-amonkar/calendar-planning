import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }
    
    # Direct flights
    direct_flights = {
        "Porto": ["Amsterdam", "Munich"],
        "Munich": ["Amsterdam", "Porto", "Reykjavik", "Prague"],
        "Reykjavik": ["Amsterdam", "Munich", "Prague"],
        "Amsterdam": ["Porto", "Munich", "Reykjavik", "Santorini", "Prague"],
        "Prague": ["Reykjavik", "Amsterdam", "Munich"],
        "Santorini": ["Amsterdam"]
    }
    
    # Fixed constraints
    constraints = [
        ("Reykjavik", (4, 7)),  # Wedding in Reykjavik between day 4 and 7
        ("Amsterdam", (14, 15)), # Conference in Amsterdam on day 14 and 15
        ("Munich", (7, 10))      # Meet friend in Munich between day 7 and 10
    ]
    
    # Total days
    total_days = 16
    
    # Generate all possible city permutations
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation satisfies all constraints
        for i in range(len(perm)):
            city = perm[i]
            days_needed = cities[city]
            
            # Check if the city can be visited in the remaining days
            if current_day + days_needed - 1 > total_days:
                valid = False
                break
            
            # Add to itinerary
            day_range = f"Day {current_day}-{current_day + days_needed - 1}"
            itinerary.append({"day_range": day_range, "place": city})
            
            # Update current day
            current_day += days_needed
            
            # Check if all days are used
            if current_day > total_days:
                break
        
        # Check if all cities are visited
        if valid and current_day > total_days:
            # Check constraints
            for city, (start, end) in constraints:
                found = False
                for entry in itinerary:
                    place = entry["place"]
                    day_range = entry["day_range"]
                    day_start = int(day_range.split('-')[0][4:])
                    day_end = int(day_range.split('-')[1])
                    
                    if place == city and day_start <= end and day_end >= start:
                        found = True
                        break
                
                if not found:
                    valid = False
                    break
            
            if valid:
                # Check flight connections
                for i in range(len(itinerary) - 1):
                    current_city = itinerary[i]["place"]
                    next_city = itinerary[i+1]["place"]
                    
                    if next_city not in direct_flights.get(current_city, []):
                        valid = False
                        break
                
                if valid:
                    return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute and print the result
print(json.dumps(find_itinerary()))