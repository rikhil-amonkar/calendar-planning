import json

def compute_itinerary():
    # Input parameters
    total_days = 17
    # Cities and required days in each destination (as specified)
    required_days = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5
    }
    
    # Direct flights between cities (bidirectional). Not used for calculation but for validating the order.
    flights = {
        ("Frankfurt", "Dublin"),
        ("Frankfurt", "London"),
        ("London", "Dublin"),
        ("Vilnius", "Frankfurt"),
        ("Frankfurt", "Stuttgart"),
        ("Dublin", "Seville"),
        ("London", "Santorini"),
        ("Stuttgart", "London"),
        ("Santorini", "Dublin")
    }
    
    # Selected Hamiltonian path (order of cities) that uses only direct flights:
    # Chosen order: Vilnius -> Frankfurt -> Stuttgart -> London -> Santorini -> Dublin -> Seville
    itinerary_order = ["Vilnius", "Frankfurt", "Stuttgart", "London", "Santorini", "Dublin", "Seville"]
    
    # Verify that adjacent cities are connected by a direct flight (flight can be used in either direction)
    for i in range(len(itinerary_order) - 1):
        city_a = itinerary_order[i]
        city_b = itinerary_order[i+1]
        if (city_a, city_b) not in flights and (city_b, city_a) not in flights:
            raise ValueError(f"No direct flight between {city_a} and {city_b}")
    
    # Note on overlapping flight day: if flying from city A to city B on day X,
    # then that day counts for both A and B.
    # Thus, if city_i has d_i required days, and the flight day is the last day 
    # (overlap with next start), then the effective timeline is:
    #   day_end[i] = day_start[i] + d_i - 1
    # and day_start[i+1] = day_end[i]
    # The total trip length becomes:
    #   sum(d_i) - (number_of_transitions)
    # For our itinerary, sum(d_i)=23, transitions=6, total = 23-6=17.
    
    itinerary = []
    current_day = 1
    for city in itinerary_order:
        days_needed = required_days[city]
        start_day = current_day
        end_day = start_day + days_needed - 1
        itinerary.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city
        })
        # Next city starts on the overlapping flight day (i.e., same as end_day)
        current_day = end_day
    
    # Final validation: the end day of the last city must equal total_days
    if current_day != total_days:
        raise ValueError("Computed itinerary does not match the total number of trip days.")
    
    return itinerary

if __name__ == "__main__":
    itinerary = compute_itinerary()
    # Output the result as JSON-formatted dictionary containing only day ranges and places.
    # We'll wrap the list with an outer dictionary with key "itinerary".
    output = {"itinerary": itinerary}
    print(json.dumps(output))