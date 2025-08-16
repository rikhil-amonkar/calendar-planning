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
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Santorini"],
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

    # Function to check if a city can be visited on a given day
    def can_visit(city, day):
        days_to_stay = constraints[city][0]
        start, end = constraints[city][1]
        if start is not None and (day < start or day + days_to_stay - 1 > end):
            return False
        for entry in itinerary:
            entry_start, entry_end = map(int, entry["day_range"].split("-")[0].split(" ")[1]), map(int, entry["day_range"].split("-")[1])
            if not (entry_end < day or entry_start > day + days_to_stay - 1):
                return False
        return True

    # Function to find the next city
    def find_next_city(current_city, current_day):
        for city, (days, (start, end)) in constraints.items():
            if can_visit(city, current_day):
                if current_city is None or city in flights[current_city]:
                    return city
        return None

    # Build the itinerary
    while current_day <= 24:
        next_city = find_next_city(current_city, current_day)
        if next_city:
            days_to_stay = constraints[next_city][0]
            if current_day + days_to_stay > 25:  # Ensure we don't exceed 24 days
                continue
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": next_city})
            current_day += days_to_stay
            current_city = next_city
        else:
            # If no valid next city is found, try to backtrack or adjust
            if itinerary:
                last_entry = itinerary.pop()
                current_day -= constraints[last_entry["place"]][0]
                current_city = itinerary[-1]["place"] if itinerary else None
            else:
                # If no valid itinerary can be formed, break
                break

    # Ensure the itinerary is exactly 24 days
    if current_day < 24:
        # Add a placeholder for remaining days if necessary
        remaining_days = 24 - current_day + 1
        if current_city:
            # Try to extend stay in the last city if possible
            days_to_stay = constraints[current_city][0]
            if remaining_days >= days_to_stay:
                itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": current_city})
                current_day += days_to_stay
        if current_day < 24:
            # Add a generic placeholder for remaining days
            itinerary.append({"day_range": f"Day {current_day}-24", "place": "Placeholder City"})

    return {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(calculate_itinerary(), indent=4))