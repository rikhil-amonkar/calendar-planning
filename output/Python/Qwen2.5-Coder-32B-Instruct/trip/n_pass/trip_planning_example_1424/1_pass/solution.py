import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Warsaw": (3, None),
        "Porto": (5, (1, 5)),
        "Naples": (4, (17, 20)),
        "Brussels": (3, (20, 22)),
        "Split": (3, None),
        "Reykjavik": (5, None),
        "Amsterdam": (4, (5, 8)),
        "Lyon": (3, None),
        "Helsinki": (4, (8, 11)),
        "Valencia": (2, None)
    }
    
    # Define the direct flight connections
    flights = [
        ("Amsterdam", "Warsaw"), ("Helsinki", "Brussels"), ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"), ("Amsterdam", "Lyon"), ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"), ("Naples", "Valencia"), ("Porto", "Brussels"),
        ("Amsterdam", "Split"), ("Lyon", "Split"), ("Warsaw", "Split"),
        ("Porto", "Amsterdam"), ("Helsinki", "Split"), ("Brussels", "Lyon"),
        ("Porto", "Lyon"), ("Reykjavik", "Warsaw"), ("Brussels", "Valencia"),
        ("Valencia", "Lyon"), ("Porto", "Warsaw"), ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"), ("Porto", "Valencia"), ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"), ("Naples", "Split"), ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"), ("Amsterdam", "Valencia"), ("Naples", "Brussels")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to check if a flight is possible
    def can_fly(from_city, to_city, day):
        return (from_city, to_city) in flights or (to_city, from_city) in flights
    
    # Helper function to find the next city to fly to
    def find_next_city(current_city, current_day):
        for city, (days, event_days) in constraints.items():
            if city != current_city and (event_days is None or (current_day + days - 1 >= event_days[0] and current_day <= event_days[1])):
                if can_fly(current_city, city, current_day):
                    return city
        return None
    
    # Start from a city with no specific start day requirement
    start_city = "Reykjavik"  # Arbitrary choice
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints[start_city][0] - 1}", "place": start_city})
    current_day += constraints[start_city][0]
    
    # Plan the rest of the itinerary
    while current_day < 28:
        next_city = find_next_city(itinerary[-1]["place"], current_day)
        if next_city:
            days_to_stay = constraints[next_city][0]
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": next_city})
            current_day += days_to_stay
        else:
            break
    
    return itinerary

# Calculate the itinerary and output it as JSON
itinerary = calculate_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output))