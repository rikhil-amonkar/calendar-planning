import json

def main():
    # Input parameters
    total_days = 14
    # Desired days in each city:
    durations = {
        "Vilnius": 4,
        "Split": 5,
        "Madrid": 6,
        "Santorini": 2
    }
    # Conference must be in Santorini on day 13 and day 14;
    # therefore Santorini has to be the final destination.
    # Available direct flight connections (bidirectional):
    direct_flights = [
        ("Vilnius", "Split"),
        ("Split", "Madrid"),
        ("Madrid", "Santorini")
    ]
    
    # For this trip, the only valid itinerary order that uses these flights,
    # meets the conference constraint in Santorini (last), and visits all cities is:
    itinerary_order = ["Vilnius", "Split", "Madrid", "Santorini"]
    
    # Validate that each consecutive pair is connected by a direct flight.
    for i in range(len(itinerary_order) - 1):
        city_a = itinerary_order[i]
        city_b = itinerary_order[i+1]
        if not ((city_a, city_b) in direct_flights or (city_b, city_a) in direct_flights):
            raise ValueError(f"No direct flight between {city_a} and {city_b}.")
    
    # Check that the overall days tally works out.
    # Because if you fly from A to B on day X, that day counts for both cities.
    # So total itinerary days = (sum of durations) - (number of flights)
    total_planned = sum(durations[city] for city in itinerary_order) - (len(itinerary_order) - 1)
    if total_planned != total_days:
        raise ValueError(f"Total planned days ({total_planned}) does not equal desired trip days ({total_days}).")
    
    # Compute itinerary day ranges.
    # For the first city, allocate its full duration.
    # For subsequent cities, the departure/arrival day overlaps.
    itinerary = []
    current_day = 1
    for index, city in enumerate(itinerary_order):
        # For the first city, we start at current_day.
        # For subsequent cities, they already start on the overlapping flight day.
        start_day = current_day
        # Since the flight day is counted in both leaving and arriving cities,
        # the city stay spans: start_day to (start_day + duration - 1)
        duration = durations[city]
        end_day = start_day + duration - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # For next leg, the flight happens on the current end_day (overlap)
        current_day = end_day
    
    # Output the itinerary as a JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()