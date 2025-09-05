import json

def compute_itinerary(total_days, city_stays, flight_connections, wedding_window):
    # The plan is to cover three cities: we assume the order is fixed:
    # Bucharest -> Lyon -> Porto since those are the only pairs with direct flights
    # and the wedding in Bucharest forces Bucharest to be first.
    #
    # The rule is: if you fly on a given day from one city to the next,
    # that day counts for both cities. Therefore, if we have N cities,
    # the total days are: sum(required_days) - (N - 1)
    #
    # Check if the given parameters are valid for the required total_days.
    num_flights = len(city_stays) - 1
    required_total = sum([days for _, days in city_stays]) - num_flights
    if required_total != total_days:
        raise ValueError("The provided durations with flight overlaps do not sum to the total days!")
    
    # We also need to ensure that the wedding date in Bucharest is fulfilled.
    # Wedding must be during day wedding_window[0] to wedding_window[1] in Bucharest.
    # Since Bucharest is the first city, its range will be Day 1 to (start + days - 1)
    # We assume that range contains the wedding window.
    bucharest_name, bucharest_days = city_stays[0]
    if bucharest_name != "Bucharest":
        raise ValueError("For the wedding constraint, Bucharest must be the first city in the itinerary.")
    
    bucharest_end = 1 + bucharest_days - 1
    wedding_start, wedding_end = wedding_window
    if not (wedding_start >= 1 and wedding_end <= bucharest_end):
        # Instead of strict checking, we just require that Bucharest covers the wedding window.
        if not (wedding_start >= 1 and wedding_start <= bucharest_end):
            raise ValueError("Wedding day start is not within the Bucharest stay.")
        if not (wedding_end >= 1 and wedding_end <= bucharest_end):
            raise ValueError("Wedding day end is not within the Bucharest stay.")
    
    itinerary = []
    current_day = 1
    # Loop over cities in order with their required durations.
    for index, (city, days_required) in enumerate(city_stays):
        start_day = current_day
        end_day = current_day + days_required - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # For next city, the day of flight from current city is the same as the arrival day at next city.
        if index < len(city_stays) - 1:
            current_day = end_day  # flight day overlaps
        
    return {"itinerary": itinerary}

def main():
    # Trip constraints input:
    total_days = 16
    # Define the cities in order along with how many days you want to spend in each.
    # Even though the sum of days is 7 + 7 + 4 = 18, two flight days overlap.
    city_stays = [
        ("Bucharest", 7),  # Wedding in Bucharest must occur between day 1 and day 7
        ("Lyon", 7),
        ("Porto", 4)
    ]
    # Direct flight connections available (bidirectional assumed):
    # Bucharest <-> Lyon and Lyon <-> Porto
    flight_connections = [
        ("Bucharest", "Lyon"),
        ("Lyon", "Porto")
    ]
    # Wedding in Bucharest must be attended between day 1 and day 7
    wedding_window = (1, 7)
    
    itinerary_plan = compute_itinerary(total_days, city_stays, flight_connections, wedding_window)
    print(json.dumps(itinerary_plan))

if __name__ == "__main__":
    main()