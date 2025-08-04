import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }
    
    fixed_events = {
        "Madrid": [(6, 7)],
        "Vienna": [(3, 6)],
        "Riga": [(20, 23)],
        "Tallinn": [(23, 27)],
        "Krakow": [(11, 15)]
    }
    
    # Define the direct flight connections
    connections = [
        ("Vienna", "Bucharest"), ("Santorini", "Madrid"), ("Seville", "Valencia"),
        ("Vienna", "Seville"), ("Madrid", "Valencia"), ("Bucharest", "Riga"),
        ("Valencia", "Bucharest"), ("Santorini", "Bucharest"), ("Vienna", "Valencia"),
        ("Vienna", "Madrid"), ("Valencia", "Krakow"), ("Valencia", "Frankfurt"),
        ("Krakow", "Frankfurt"), ("Riga", "Tallinn"), ("Vienna", "Krakow"),
        ("Vienna", "Frankfurt"), ("Madrid", "Seville"), ("Santorini", "Vienna"),
        ("Vienna", "Riga"), ("Frankfurt", "Tallinn"), ("Frankfurt", "Bucharest"),
        ("Madrid", "Bucharest"), ("Frankfurt", "Riga"), ("Madrid", "Frankfurt")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to check if a place can be visited on a given day
    def can_visit(place, day):
        for event_days in fixed_events.get(place, []):
            if event_days[0] <= day <= event_days[1]:
                return True
        return False
    
    # Helper function to find the next possible place to visit
    def find_next_place(current_place, current_day):
        for place, duration in constraints.items():
            if place != current_place and (current_place, place) in connections:
                for day in range(current_day, current_day + duration + 1):
                    if can_visit(place, day):
                        return place, day
        return None, None
    
    # Start with Santorini since it has a fixed duration
    current_place = "Santorini"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints[current_place] - 1}", "place": current_place})
    current_day += constraints[current_place]
    
    # Plan the rest of the itinerary
    while current_day < 28:
        next_place, next_day = find_next_place(current_place, current_day)
        if next_place:
            itinerary.append({"day_range": f"Day {next_day}-{next_day + constraints[next_place] - 1}", "place": next_place})
            current_day = next_day + constraints[next_place]
            current_place = next_place
        else:
            break
    
    return itinerary

# Calculate the itinerary and output it as JSON
itinerary = calculate_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output))