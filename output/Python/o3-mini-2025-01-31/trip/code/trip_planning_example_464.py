import json

def main():
    # Trip parameters
    total_days = 18
    # Required stay days in each city (the day when flying counts for both)
    required = {
        "Krakow": 5,
        "Frankfurt": 4,
        "Dubrovnik": 5,
        "Naples": 5,
        "Oslo": 3
    }
    
    # Special constraints:
    # - In Dubrovnik, you want to meet your friends between day 5 and day 9.
    friends_window = (5, 9)
    # - In Oslo, you plan to visit relatives between day 16 and day 18.
    relatives_window = (16, 18)
    
    # Flight connectivity (bidirectional assumed)
    direct_flights = {
        ("Dubrovnik", "Oslo"),
        ("Frankfurt", "Krakow"),
        ("Frankfurt", "Oslo"),
        ("Dubrovnik", "Frankfurt"),
        ("Krakow", "Oslo"),
        ("Naples", "Oslo"),
        ("Naples", "Dubrovnik"),
        ("Naples", "Frankfurt")
    }
    # For our chosen itinerary, the flight sequence (with flight days that count in both cities) is:
    itinerary_order = ["Krakow", "Frankfurt", "Dubrovnik", "Naples", "Oslo"]
    
    # Verify that each consecutive flight is allowed (bidirectional check)
    for i in range(len(itinerary_order) - 1):
        city_from = itinerary_order[i]
        city_to = itinerary_order[i+1]
        if (city_from, city_to) not in direct_flights and (city_to, city_from) not in direct_flights:
            raise ValueError(f"No direct flight exists between {city_from} and {city_to}.")
    
    # The idea is to assign each segment an interval [start_day, end_day] such that:
    #   For the first city: duration = required[city]
    #   For each subsequent city, we assume the flight takes place on the starting day.
    #   That day is counted in both the previous and next city.
    # Hence, for city i (after the first):
    #   start_day = previous city's end_day (overlap flight day)
    #   end_day = start_day + required[city] - 1
    
    itinerary = []
    current_start = 1
    for city in itinerary_order:
        days_needed = required[city]
        end_day = current_start + days_needed - 1
        itinerary.append({
            "day_range": f"{current_start}-{end_day}",
            "place": city
        })
        # Next city will start on the same day as this city's end_day
        current_start = end_day

    # Check that total trip ends exactly at total_days
    if itinerary[-1]["day_range"].split("-")[-1] != str(total_days):
        # Convert the last day_range and adjust if necessary
        last_segment = itinerary[-1]
        _, last_end = map(int, last_segment["day_range"].split("-"))
        if last_end != total_days:
            raise ValueError("The computed itinerary does not match the total trip duration.")

    # Check that special constraints are satisfied:
    # Dubrovnik friends meeting: at least one day in Dubrovnik between day 5 and 9.
    dubrovnik_segment = next(seg for seg in itinerary if seg["place"] == "Dubrovnik")
    dub_start, dub_end = map(int, dubrovnik_segment["day_range"].split("-"))
    friends_ok = (friends_window[0] <= dub_start <= friends_window[1]) or (friends_window[0] <= dub_end <= friends_window[1]) or (dub_start < friends_window[0] and dub_end > friends_window[1])
    if not friends_ok:
        raise ValueError("Dubrovnik visit does not include the friends meeting window between day 5 and 9.")
    
    # Oslo relatives visit: Oslo segment must include at least one day within day 16 and 18.
    oslo_segment = next(seg for seg in itinerary if seg["place"] == "Oslo")
    oslo_start, oslo_end = map(int, oslo_segment["day_range"].split("-"))
    relatives_ok = (relatives_window[0] <= oslo_start <= relatives_window[1]) or (relatives_window[0] <= oslo_end <= relatives_window[1]) or (oslo_start < relatives_window[0] and oslo_end > relatives_window[1])
    if not relatives_ok:
        raise ValueError("Oslo visit does not include the relatives window between day 16 and 18.")
    
    # Output the final itinerary in JSON format
    print(json.dumps(itinerary, indent=4))

if __name__ == '__main__':
    main()