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
    
    # Helper function to find the next possible city
    def find_next_city(current_city, current_day):
        for city, (days, (start, end)) in constraints.items():
            if start is not None and (current_day < start or current_day > end):
                continue
            if any((city, days) in segment for segment in itinerary):
                continue
            if (current_city, city) in flights or (city, current_city) in flights:
                return city, days
        return None, None
    
    # Start from Geneva due to the early visit to relatives
    current_city = "Geneva"
    itinerary.append((current_city, constraints[current_city][0], current_day))
    current_day += constraints[current_city][0]
    
    # Fill the itinerary based on constraints and available flights
    while current_day <= 27:
        next_city, days_to_stay = find_next_city(current_city, current_day)
        if next_city is None:
            break
        itinerary.append((next_city, days_to_stay, current_day))
        current_day += days_to_stay
        current_city = next_city
    
    # Format the itinerary as required
    formatted_itinerary = []
    for city, days, start_day in itinerary:
        end_day = start_day + days - 1
        formatted_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    return {"itinerary": formatted_itinerary}

# Output the result as JSON
print(json.dumps(calculate_itinerary(), indent=4))