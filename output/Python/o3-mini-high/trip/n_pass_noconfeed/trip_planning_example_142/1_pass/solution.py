import json

def compute_itinerary(total_days, days_madrid, days_dublin, days_tallinn, workshop_range, flights):
    # Verify that the required route Madrid -> Dublin -> Tallinn exists based on direct flights available.
    if ('Madrid', 'Dublin') not in flights and ('Dublin', 'Madrid') not in flights:
        raise Exception("No direct flight available between Madrid and Dublin.")
    if ('Dublin', 'Tallinn') not in flights and ('Tallinn', 'Dublin') not in flights:
        raise Exception("No direct flight available between Dublin and Tallinn.")

    # Check if overall day allocation (with overlapping flight days) sums correctly.
    # When flying, the departure day is counted for both the origin and destination.
    # Hence the unique count of days is: (days_madrid + days_dublin + days_tallinn - 2)
    if days_madrid + days_dublin + days_tallinn - 2 != total_days:
        raise Exception("The sum of allocated days (adjusted for flight overlaps) does not equal total_days.")

    # Determine the flight days.
    # Assume the following:
    # - Start in Madrid. Fly from Madrid to Dublin on the day that ends Madrid's count.
    # - Since the flight day counts for both, if we need 4 days in Madrid, we leave on Day 4.
    # - Arriving in Dublin on Day 4, we need 3 days in Dublin. With Day 4 counted already, we leave on Day (4 + 3 - 1) = Day 6.
    # - Arriving in Tallinn on Day 6, we then cover Tallinn until the end (Day 7).
    flight_day_madrid_to_dublin = days_madrid  # Day 4
    flight_day_dublin_to_tallinn = days_madrid + days_dublin - 1  # Day 6

    # Tallinn itinerary runs from the flight day until the end.
    tallinn_start_day = flight_day_dublin_to_tallinn
    tallinn_end_day = total_days

    # Check workshop constraint: the workshop in Tallinn must occur between workshop_range.
    # Ensure that the Tallinn period (which is inclusive) overlaps with the workshop window.
    workshop_start, workshop_end = workshop_range
    if tallinn_end_day < workshop_start or tallinn_start_day > workshop_end:
        raise Exception("The workshop constraint in Tallinn cannot be satisfied with the current itinerary.")

    # Create the itinerary with overlapping flight days.
    itinerary = []
    itinerary.append({
        "day_range": "Day {}-{}".format(1, flight_day_madrid_to_dublin),
        "place": "Madrid"
    })
    itinerary.append({
        "day_range": "Day {}-{}".format(flight_day_madrid_to_dublin, flight_day_dublin_to_tallinn),
        "place": "Dublin"
    })
    itinerary.append({
        "day_range": "Day {}-{}".format(flight_day_dublin_to_tallinn, total_days),
        "place": "Tallinn"
    })

    return {"itinerary": itinerary}

def main():
    # Define input constraints
    total_days = 7
    days_madrid = 4  # Including the flight day which is shared
    days_dublin = 3  # Including the flight day(s) which are shared
    days_tallinn = 2
    # Workshop in Tallinn must fall between day 6 and day 7 (inclusive)
    workshop_range = (6, 7)
    
    # List of available direct flights (bidirectional where applicable)
    flights = [
        ("Madrid", "Dublin"),
        ("Dublin", "Madrid"),
        ("Dublin", "Tallinn"),
        ("Tallinn", "Dublin")
    ]

    itinerary_plan = compute_itinerary(total_days, days_madrid, days_dublin, days_tallinn, workshop_range, flights)
    print(json.dumps(itinerary_plan))

if __name__ == '__main__':
    main()