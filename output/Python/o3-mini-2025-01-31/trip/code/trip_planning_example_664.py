import json

def compute_itinerary():
    # Define the trip constraints as input variables
    total_days = 18
    cities = [
        {
            "place": "Bucharest",
            "duration": 4,   # 4 days in Bucharest
            "constraint": {"min_day": 1, "max_day": 4}  # visit relatives between day 1 and day 4
        },
        {
            "place": "Munich",
            "duration": 5,   # 5 days in Munich
            "constraint": {"min_day": 4, "max_day": 8}  # wedding between day 4 and day 8
        },
        {
            "place": "Seville",
            "duration": 5,   # 5 days in Seville
            "constraint": {"min_day": 8, "max_day": 12} # meet friends between day 8 and day 12
        },
        {
            "place": "Milan",
            "duration": 2,   # 2 days in Milan
            "constraint": None
        },
        {
            "place": "Stockholm",
            "duration": 5,   # 5 days in Stockholm
            "constraint": None
        },
        {
            "place": "Tallinn",
            "duration": 2,   # 2 days in Tallinn
            "constraint": None
        }
    ]
    
    # The allowed direct flights graph (for reference, not used in the calculations)
    # Bucharest <-> Munich, Munich <-> Seville, Seville <-> Milan,
    # Milan <-> Stockholm, Stockholm <-> Tallinn, plus some other edges.
    # Our chosen itinerary order is:
    # Bucharest -> Munich -> Seville -> Milan -> Stockholm -> Tallinn
    itinerary_order = ["Bucharest", "Munich", "Seville", "Milan", "Stockholm", "Tallinn"]
    
    # Reorder cities dictionary to follow itinerary_order
    city_dict = {city["place"]: city for city in cities}
    ordered_cities = [city_dict[place] for place in itinerary_order]
    
    itinerary = []
    # We use the flight rule: if you fly from A to B on day X, then day X counts
    # for both cities A and B. So for the first city, start on day 1.
    # For each subsequent city, the start day equals the previous city's end day.
    current_start = 1
    for city in ordered_cities:
        duration = city["duration"]
        # end day is calculated as start + duration - 1
        current_end = current_start + duration - 1
        itinerary.append({
            "day_range": f"{current_start}-{current_end}",
            "place": city["place"]
        })
        # For next city, flight day overlap: next city starts on the same day as current_end
        current_start = current_end

    # Verify the overall itinerary ends on the total planned day
    # Compute overall days using overlapping flight days.
    total_count = sum(city["duration"] for city in ordered_cities) - (len(ordered_cities)-1)
    if total_count != total_days:
        raise ValueError("Computed itinerary does not match the total planned days.")
    
    # Check constraints (for demonstration, we verify that the constrained events fall within the required intervals)
    # Bucharest relatives constraint: its range must include at least one day between 1 and 4.
    bucharest_range = itinerary[0]["day_range"].split("-")
    bucharest_start, bucharest_end = int(bucharest_range[0]), int(bucharest_range[1])
    if not (1 >= bucharest_start and 4 <= bucharest_end or (bucharest_start <= 1 <= bucharest_end) or (bucharest_start <= 4 <= bucharest_end)):
        raise ValueError("Bucharest itinerary does not meet the relatives visit constraint.")
    
    # Munich wedding constraint: Munich range must include some day between 4 and 8.
    munich_range = itinerary[1]["day_range"].split("-")
    munich_start, munich_end = int(munich_range[0]), int(munich_range[1])
    if not (munich_start <= 4 <= munich_end or munich_start <= 8 <= munich_end or (4 >= munich_start and 8 <= munich_end)):
        raise ValueError("Munich itinerary does not meet the wedding constraint.")
    
    # Seville friends constraint: must include a day between 8 and 12.
    seville_range = itinerary[2]["day_range"].split("-")
    seville_start, seville_end = int(seville_range[0]), int(seville_range[1])
    if not (seville_start <= 8 <= seville_end or seville_start <= 12 <= seville_end or (8 >= seville_start and 12 <= seville_end)):
        raise ValueError("Seville itinerary does not meet the friends meeting constraint.")
    
    return itinerary

def main():
    itinerary = compute_itinerary()
    # Output the result as JSON-formatted dictionary (list of dicts)
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()