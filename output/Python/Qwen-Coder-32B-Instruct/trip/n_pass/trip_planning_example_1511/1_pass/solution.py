import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Venice": (3, [None, None]),
        "Reykjavik": (2, [None, None]),
        "Munich": (3, [4, 6]),
        "Santorini": (3, [8, 10]),
        "Manchester": (3, [None, None]),
        "Porto": (3, [None, None]),
        "Bucharest": (5, [None, None]),
        "Tallinn": (4, [None, None]),
        "Valencia": (2, [14, 15]),
        "Vienna": (5, [None, None])
    }

    # Define the flight connections
    flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Santorni"],
        "Manchester": ["Bucharest", "Vienna", "Santorini", "Porto"],
        "Munich": ["Venice", "Porto", "Reykjavik", "Manchester", "Vienna", "Bucharest", "Tallinn", "Valencia"],
        "Santorini": ["Venice", "Manchester", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Santorini", "Manchester", "Porto", "Venice", "Munich", "Bucharest"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Reykjavik": ["Vienna", "Munich"],
        "Porto": ["Manchester", "Vienna", "Munich", "Valencia"],
        "Tallinn": ["Munich"],
        "Valencia": ["Bucharest", "Vienna", "Porto", "Munich"]
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None

    # Function to find the next city
    def find_next_city(current_city, current_day):
        for city, (days, (start, end)) in constraints.items():
            if start is None or (current_day >= start and current_day <= end):
                if all(day is None for day in range(current_day, current_day + days)):
                    if current_city is None or city in flights[current_city]:
                        return city
        return None

    # Build the itinerary
    while current_day <= 24:
        next_city = find_next_city(current_city, current_day)
        if next_city:
            days_to_stay = constraints[next_city][0]
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": next_city})
            current_day += days_to_stay
            current_city = next_city
        else:
            current_day += 1

    return {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(calculate_itinerary(), indent=4))