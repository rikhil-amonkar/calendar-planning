import json

def calculate_itinerary(total_days, naples_days, vienna_days, vilnius_days, relatives_window, flight_connections):
    # Check that the required direct flights exist
    if ('Naples', 'Vienna') not in flight_connections or ('Vienna', 'Vilnius') not in flight_connections:
        raise ValueError("Required direct flight connections are not available for the planned itinerary.")
    
    itinerary = []
    day_start = 1

    # Plan Naples segment.
    # Since visiting relatives in Naples must occur between day 1 and day 5, we start here.
    naples_start = day_start
    naples_end = naples_start + naples_days - 1  # Flight day from Naples to Vienna is included in Naples_days

    # Verify relatives constraint: At least one Naples day must fall within the relative visiting window.
    if naples_start > relatives_window[1] or naples_end < relatives_window[0]:
        raise ValueError("Naples visit does not fall within the required relative visit window (Day {}-{}).".format(*relatives_window))
    
    itinerary.append({
        "day_range": f"Day {naples_start}-{naples_end}",
        "place": "Naples"
    })

    # Plan Vienna segment.
    # Flight from Naples to Vienna takes place on the same day as the end of the Naples segment.
    vienna_start = naples_end  # Flight day counts for both cities.
    vienna_end = vienna_start + vienna_days - 1
    itinerary.append({
        "day_range": f"Day {vienna_start}-{vienna_end}",
        "place": "Vienna"
    })

    # Plan Vilnius segment.
    # Flight from Vienna to Vilnius occurs on the same day as the end of the Vienna segment.
    vilnius_start = vienna_end  # Overlap day
    vilnius_end = vilnius_start + vilnius_days - 1
    itinerary.append({
        "day_range": f"Day {vilnius_start}-{vilnius_end}",
        "place": "Vilnius"
    })

    # Check that our computed itinerary fits into the total trip days.
    if vilnius_end != total_days:
        raise ValueError("The computed itinerary does not match the total trip days of {}.".format(total_days))
    
    return {"itinerary": itinerary}

def main():
    # Input variables based on trip constraints
    total_days = 17
    naples_days = 5
    vienna_days = 7
    vilnius_days = 7
    relatives_window = (1, 5)  # Must visit relatives in Naples between Day 1 and Day 5
    flight_connections = {
        ("Naples", "Vienna"),
        ("Vienna", "Naples"),
        ("Vienna", "Vilnius"),
        ("Vilnius", "Vienna")
    }
    
    itinerary_plan = calculate_itinerary(total_days, naples_days, vienna_days, vilnius_days, relatives_window, flight_connections)
    print(json.dumps(itinerary_plan))

if __name__ == "__main__":
    main()