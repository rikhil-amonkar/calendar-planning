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
    
    direct_flights = [
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
    
    # Helper function to find the next possible city to fly to
    def find_next_city(current_city, day):
        for city in constraints:
            if constraints[city] > 0 and (current_city, city) in direct_flights:
                if can_visit(city, day):
                    return city
        return None
    
    # Main loop to build the itinerary
    while current_day <= 27:
        for city in constraints:
            if constraints[city] > 0:
                if can_visit(city, current_day):
                    start_day = current_day
                    end_day = min(start_day + constraints[city] - 1, 27)
                    while end_day > start_day and not can_visit(city, end_day):
                        end_day -= 1
                    duration = end_day - start_day + 1
                    if duration > 0:
                        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                        current_day = end_day + 1
                        constraints[city] -= duration
                        break
        else:
            # If no city can be visited, try to find a flight to another city
            next_city = find_next_city(itinerary[-1]["place"], current_day)
            if next_city:
                itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": next_city})
                current_day += 1
            else:
                current_day += 1
    
    return {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(calculate_itinerary(), indent=4))