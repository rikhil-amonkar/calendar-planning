import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Paris": (5, None),
        "Florence": (3, None),
        "Vienna": (2, (19, 20)),
        "Porto": (3, (1, 3)),
        "Munich": (5, None),
        "Nice": (5, None),
        "Warsaw": (3, (13, 15))
    }
    
    # Define the direct flight connections
    flights = [
        ("Florence", "Vienna"), ("Paris", "Warsaw"), ("Munich", "Vienna"), 
        ("Porto", "Vienna"), ("Warsaw", "Vienna"), ("Florence", "Munich"), 
        ("Munich", "Warsaw"), ("Munich", "Nice"), ("Paris", "Florence"), 
        ("Warsaw", "Nice"), ("Porto", "Munich"), ("Porto", "Nice"), 
        ("Paris", "Vienna"), ("Nice", "Vienna"), ("Porto", "Paris"), 
        ("Paris", "Nice"), ("Paris", "Munich"), ("Porto", "Warsaw")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Function to check if a city can be visited on a given day
    def can_visit(city, day):
        if city in constraints:
            min_days, specific_days = constraints[city]
            if specific_days:
                return specific_days[0] <= day <= specific_days[1]
            else:
                return True
        return False
    
    # Function to find the next possible city to visit
    def find_next_city(current_city, current_day):
        for city in constraints:
            if can_visit(city, current_day) and (current_city, city) in flights:
                return city
        return None
    
    # Build the itinerary
    for city, (days, _) in constraints.items():
        if can_visit(city, current_day):
            start_day = current_day
            while current_day < start_day + days:
                next_city = find_next_city(city, current_day)
                if next_city and can_visit(next_city, current_day + 1):
                    break
                current_day += 1
            itinerary.append({"day_range": f"Day {start_day}-{current_day}", "place": city})
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))