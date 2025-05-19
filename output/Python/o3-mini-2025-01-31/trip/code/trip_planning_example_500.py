import json

def compute_itinerary():
    # Input parameters based on constraints:
    total_days = 20

    # Cities and required durations (total days if isolated)
    # Note: Flight days count for both origin and destination.
    # To account for total trip days, we'll have 4 flight overlaps.
    cities = [
        {"name": "Hamburg", "required": 7},
        {"name": "Split", "required": 7},
        {"name": "Lyon", "required": 2},
        {"name": "Munich", "required": 6},
        {"name": "Manchester", "required": 2}
    ]

    # Flight connectivity (bidirectional if stated as "and" except one directional case).
    # Provided edges:
    #   Split-Munich, Munich-Manchester, Hamburg-Manchester, Hamburg-Munich,
    #   Split-Lyon, Lyon-Munich, Hamburg-Split, and a one-directional flight from Manchester to Split.
    # We choose an ordering that satisfies all constraints:
    #   The itinerary ordering selected is:
    #     1. Hamburg
    #     2. Split
    #     3. Lyon   (Annual show on days 13-14)
    #     4. Munich (6 days stay)
    #     5. Manchester (Relatives between day 19 and day 20)
    #
    # Flight validation for this ordering:
    #   Hamburg -> Split (direct: Hamburg and Split exist)
    #   Split -> Lyon (direct: Split and Lyon exist)
    #   Lyon -> Munich (direct: Lyon and Munich exist)
    #   Munich -> Manchester (direct: Munich and Manchester exist)
    
    # The flight effect: if flying from city A to city B on day X,
    # then day X counts for both A and B.
    # With 5 cities and 4 flights, the naive sum of required days is 7 + 7 + 2 + 6 + 2 = 24.
    # Subtracting 4 overlapping flight days gives: 24 - 4 = 20 days total.
    
    itinerary = []
    current_day = 1

    # For the first city, there is no overlap from a previous flight.
    first_city = cities[0]
    first_start = current_day
    first_end = first_start + first_city["required"] - 1  # no overlap adjustment for the first segment
    itinerary.append({"day_range": f"{first_start}-{first_end}", "place": first_city["name"]})
    current_day = first_end  # this day is shared with the next city as flight day

    # For subsequent cities, each city gets its required days with first day already being the flight overlap day.
    for city in cities[1:]:
        start = current_day  # flight day; already in previous city at end, now also count as first day for current city
        end = start + city["required"] - 1  # additional days
        itinerary.append({"day_range": f"{start}-{end}", "place": city["name"]})
        current_day = end  # next flight will share this day

    # Validate special constraints:
    # 1. Annual show in Lyon on day 13 to day 14
    # 2. Visit relatives in Manchester between day 19 and day 20
    def extract_range(itinerary, city_name):
        for item in itinerary:
            if item["place"] == city_name:
                start_str, end_str = item["day_range"].split("-")
                return int(start_str), int(end_str)
        return None, None

    lyon_start, lyon_end = extract_range(itinerary, "Lyon")
    manchester_start, manchester_end = extract_range(itinerary, "Manchester")
    
    if lyon_start != 13 or lyon_end != 14:
        raise ValueError("Lyon must be visited on days 13 to 14 to attend the annual show.")
    if manchester_start != 19 or manchester_end != 20:
        raise ValueError("Manchester must be visited on days 19 to 20 to visit relatives.")

    # Final check: the overall trip should span total_days = 20 days (accounting overlaps)
    # The computed itinerary's last day should be equal to total_days
    if current_day != total_days:
        raise ValueError("The computed itinerary does not span the required total of 20 days.")

    return itinerary

if __name__ == "__main__":
    itinerary = compute_itinerary()
    # Output the itinerary as a JSON formatted dictionary with only day_ranges and places
    print(json.dumps(itinerary))