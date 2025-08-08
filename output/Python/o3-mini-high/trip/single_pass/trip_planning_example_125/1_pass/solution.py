#!/usr/bin/env python3
import itertools
import json

def compute_itinerary():
    # Input constraints
    total_trip_days = 15
    # Required durations in each city (the "city-day visits")
    city_durations = {
        "Stuttgart": 6,
        "Seville": 7,
        "Manchester": 4
    }
    # Friend meeting constraint: Must meet friend in Stuttgart between day 1 and day 6.
    friend_city = "Stuttgart"
    friend_meeting_window = (1, 6)  # (earliest_day, latest_day)
    
    # Direct flights available (bidirectional)
    # The tuple (A, B) means there is a direct flight from A to B.
    direct_flights = {
        ("Manchester", "Seville"),
        ("Seville", "Manchester"),
        ("Stuttgart", "Manchester"),
        ("Manchester", "Stuttgart")
    }
    
    cities = list(city_durations.keys())
    
    # Function to check if a given itinerary ordering has valid direct flights.
    def has_valid_connections(order):
        for i in range(len(order) - 1):
            if (order[i], order[i+1]) not in direct_flights:
                return False
        return True
    
    # Given an order, assign day ranges for each city.
    # Rule: For the first city, start_day = 1.
    # When flying from one city to the next, the flight day is the last day of the previous city,
    # which counts as a day in both cities.
    def assign_day_ranges(order):
        itinerary_days = []
        current_day = 1
        for city in order:
            start_day = current_day
            # The city is visited for a full number of days.
            # Because if you fly on the last day, that day is double-counted.
            duration = city_durations[city]
            end_day = start_day + duration - 1
            itinerary_days.append((city, start_day, end_day))
            # If not the last city, the next city's start day is the same as this city's end day
            # (because that day counts for both departure and arrival).
            current_day = end_day
        return itinerary_days

    # Check if the friend meeting constraint is met:
    # The friend meeting in Stuttgart must occur on some day in Stuttgart that falls within the window.
    # We require that Stuttgart's stay begins no later than the last acceptable day.
    def friend_meeting_ok(itinerary_days):
        for city, start_day, end_day in itinerary_days:
            if city == friend_city:
                # If at least one day of stay in Stuttgart falls within the friend meeting window.
                # Since days are consecutive, if the start_day is less than or equal to the latest possible meeting day,
                # then we can have a meeting day.
                if start_day <= friend_meeting_window[1]:
                    return True
        return False

    valid_itinerary = None
    # Explore all permutations of the cities.
    for order in itertools.permutations(cities):
        if not has_valid_connections(order):
            continue
        itinerary_days = assign_day_ranges(order)
        # The total trip length is the end_day of the last city.
        if itinerary_days[-1][2] != total_trip_days:
            continue
        if not friend_meeting_ok(itinerary_days):
            continue
        valid_itinerary = itinerary_days
        break

    return valid_itinerary

def main():
    itinerary_days = compute_itinerary()
    if not itinerary_days:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start_day, end_day in itinerary_days:
            day_range = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()