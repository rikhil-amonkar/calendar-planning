#!/usr/bin/env python3
import json

def plan_itinerary(total_days, days_madrid, days_dublin, days_tallinn,
                   workshop_day_range, direct_flights):
    # We know available direct flights: Madrid <-> Dublin and Dublin <-> Tallinn
    # We have the additional rule that if a flight occurs from A to B on day X,
    # then day X counts for both A and B.
    # Our goal is to schedule the trip over 'total_days' days (days 1 through total_days)
    #
    # Based on the constraints:
    # - Madrid must be 4 days.
    # - Dublin must be 3 days.
    # - Tallinn must be 2 days.
    # - A flight from Madrid to Dublin must be taken.
    # - A flight from Dublin to Tallinn must be taken.
    # - Workshop in Tallinn must be attended between workshop_day_range (e.g., day 6 and day 7).
    #
    # One viable itinerary strategy (with overlapping flight days):
    # 1. Start in Madrid and remain there until day F1, where flight from Madrid to Dublin occurs.
    #    Let F1 be the flight day. Madrid will count days 1 ... F1.
    # 2. After that, remain in Dublin until day F2, when flight from Dublin to Tallinn occurs.
    #    Dublin will count days F1 ... F2.
    # 3. Conclude in Tallinn from day F2 to day total_days.
    #    Tallinn will count days F2 ... total_days.
    #
    # The counts including flight days:
    # Madrid count = F1 - 1 + 1 = F1  (days 1 through F1)
    # Dublin count = (F2 - F1 + 1)
    # Tallinn count = (total_days - F2 + 1)
    #
    # We have the following equations:
    #   F1 = days_madrid
    #   F2 - F1 + 1 = days_dublin  --> F2 = days_dublin + F1 - 1 = days_dublin + days_madrid - 1
    #   total_days - F2 + 1 = days_tallinn  --> F2 = total_days - days_tallinn + 1
    #
    # Therefore, for the constraints to be consistent, we need:
    #   days_dublin + days_madrid - 1 = total_days - days_tallinn + 1
    # Let's check that:
    #   LHS = days_dublin + days_madrid - 1
    #   RHS = total_days - days_tallinn + 1
    #
    # For our given numbers:
    #   days_madrid = 4, days_dublin = 3, days_tallinn = 2, total_days = 7
    #   LHS = 3 + 4 - 1 = 6
    #   RHS = 7 - 2 + 1 = 6
    #
    # So the constraints match.
    #
    # Let's choose:
    F1 = days_madrid  # flight from Madrid on day F1 counts for both Madrid and Dublin
    F2 = F1 + days_dublin - 1  # flight from Dublin to Tallinn on day F2 counts for both Dublin and Tallinn

    # Ensure that the Tallinn workshop requirement is satisfied:
    # The workshop in Tallinn must be attended between workshop_day_range[0] and workshop_day_range[1]
    # This requires that at least one of F2 or total_days (the Tallinn days) falls in that range.
    # We'll check if workshop_day_range intersect the Tallinn days [F2, total_days] is not empty.
    tallinn_days = set(range(F2, total_days + 1))
    workshop_days = set(range(workshop_day_range[0], workshop_day_range[1] + 1))
    if tallinn_days.isdisjoint(workshop_days):
        raise ValueError("Itinerary cannot satisfy the Tallinn workshop constraint.")

    # Build itinerary segments
    # Each segment is defined by a day range (which can be a flight day overlap) and place.
    itinerary = []
    # Madrid segment: day 1 to F1
    itinerary.append({
        "day_range": f"1-{F1}",
        "place": "Madrid"
    })
    # Dublin segment: day F1 to F2
    itinerary.append({
        "day_range": f"{F1}-{F2}",
        "place": "Dublin"
    })
    # Tallinn segment: day F2 to total_days
    itinerary.append({
        "day_range": f"{F2}-{total_days}",
        "place": "Tallinn"
    })

    return itinerary

def main():
    # Input constraints
    total_days = 7
    days_madrid = 4
    days_dublin = 3
    days_tallinn = 2
    workshop_day_range = (6, 7)  # workshop in Tallinn must be between day 6 and day 7 inclusive

    # Available direct flights: Madrid <-> Dublin, Dublin <-> Tallinn
    direct_flights = [
        ("Madrid", "Dublin"),
        ("Dublin", "Tallinn")
    ]

    itinerary = plan_itinerary(total_days, days_madrid, days_dublin, days_tallinn,
                               workshop_day_range, direct_flights)
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()