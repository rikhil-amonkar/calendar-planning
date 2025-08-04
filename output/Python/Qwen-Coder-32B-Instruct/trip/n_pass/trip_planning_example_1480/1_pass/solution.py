import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Istanbul": (4, [None, None]),
        "Vienna": (4, [None, None]),
        "Riga": (2, [None, None]),
        "Brussels": (2, [26, 27]),
        "Madrid": (4, [None, None]),
        "Vilnius": (4, [20, 23]),
        "Venice": (5, [7, 11]),
        "Geneva": (4, [1, 4]),
        "Munich": (5, [None, None]),
        "Reykjavik": (2, [None, None])
    }
    
    # Define the direct flight connections
    flights = [
        ("Munich", "Vienna"), ("Istanbul", "Brussels"), ("Vienna", "Vilnius"),
        ("Madrid", "Munich"), ("Venice", "Brussels"), ("Riga", "Brussels"),
        ("Geneva", "Istanbul"), ("Munich", "Reykjavik"), ("Vienna", "Istanbul"),
        ("Riga", "Istanbul"), ("Reykjavik", "Vienna"), ("Venice", "Munich"),
        ("Madrid", "Venice"), ("Vilnius", "Istanbul"), ("Venice", "Vienna"),
        ("Venice", "Istanbul"), ("Reykjavik", "Madrid"), ("Riga", "Munich"),
        ("Munich", "Istanbul"), ("Reykjavik", "Brussels"), ("Vilnius", "Brussels"),
        ("Vilnius", "Munich"), ("Madrid", "Vienna"), ("Vienna", "Riga"),
        ("Geneva", "Vienna"), ("Madrid", "Brussels"), ("Vienna", "Brussels"),
        ("Geneva", "Brussels"), ("Geneva", "Madrid"), ("Munich", "Brussels"),
        ("Madrid", "Istanbul"), ("Geneva", "Munich"), ("Riga", "Vilnius")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Function to find the next possible city
    def find_next_city(current_city, current_day):
        for city, (days, (start, end)) in constraints.items():
            if start is not None and (current_day < start or current_day > end):
                continue
            if any(city == i['place'] for i in itinerary):
                continue
            for flight in flights:
                if flight[0] == current_city and flight[1] == city:
                    return city
        return None
    
    # Start from Geneva as per the visit to relatives constraint
    current_city = "Geneva"
    while current_day <= 27:
        # Find the next city to visit
        next_city = find_next_city(current_city, current_day)
        if next_city is None:
            break
        
        # Determine the number of days to stay in the current city
        days_to_stay = constraints[current_city][0]
        if constraints[current_city][1][0] is not None:
            days_to_stay = max(days_to_stay, constraints[current_city][1][1] - current_day + 1)
        
        # Add the current city to the itinerary
        itinerary.append({
            "day_range": f"Day {current_day}-{current_day + days_to_stay - 1}",
            "place": current_city
        })
        
        # Move to the next city
        current_day += days_to_stay
        current_city = next_city
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())