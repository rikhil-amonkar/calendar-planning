#!/usr/bin/env python3
import json

def main():
    # Trip constraints as input variables
    total_days = 7
    required_durations = {
        "Madrid": 4,   # total days in Madrid (including flight day)
        "Dublin": 3,   # total days in Dublin (including flight day)
        "Tallinn": 2   # total days in Tallinn (including flight day)
    }
    # Available direct flights: Madrid <-> Dublin, Dublin <-> Tallinn
    direct_flights = [("Madrid", "Dublin"), ("Dublin", "Tallinn")]
    # Workshop in Tallinn must be attended between day 6 and day 7 (inclusive)
    workshop_start = 6
    workshop_end = 7

    # We assume the only valid order given the direct flights is:
    # Madrid -> Dublin -> Tallinn
    # With flight transitions:
    # If flight from city A to city B is on day X,
    # then day X counts for both A and B.
    
    # Determine the flight day from Madrid to Dublin.
    # To achieve the required 4 days for Madrid, we set the flight from Madrid
    # to Dublin on the day equal to Madrid's required duration.
    flight_day_Madrid_Dublin = required_durations["Madrid"]  # Day 4

    # Determine the flight day from Dublin to Tallinn.
    # Dublin's counted days include the arrival day (which is flight_day_Madrid_Dublin)
    # and the flight day to Tallinn. So,
    # (flight_day_Dublin_to_Tallinn - flight_day_Madrid_Dublin + 1) must equal required_durations["Dublin"].
    flight_day_Dublin_Tallinn = flight_day_Madrid_Dublin + required_durations["Dublin"] - 1  # Day 4 + 3 - 1 = Day 6

    # Now, calculate the actual counted duration in Tallinn:
    tallinn_counted = total_days - flight_day_Dublin_Tallinn + 1  # Days from flight day to total day inclusive
    if tallinn_counted != required_durations["Tallinn"]:
        result = {"error": "The itinerary constraints cannot be satisfied with the given parameters."}
        print(json.dumps(result))
        return

    # Verify that the workshop in Tallinn can be attended between day 6 and day 7.
    # Since the flight to Tallinn is on flight_day_Dublin_Tallinn and Tallinn is counted on that day,
    # we check that flight_day_Dublin_Tallinn falls within the workshop window.
    if not (workshop_start <= flight_day_Dublin_Tallinn <= workshop_end):
        result = {"error": "Tallinn visit does not satisfy the workshop schedule constraints."}
        print(json.dumps(result))
        return

    # Build the itinerary using calculated flight days.
    # Note: If a flight happens on day X, the traveler is counted in both cities on day X.
    itinerary = []
    # Madrid: from day 1 to flight_day_Madrid_Dublin (Day 1-4)
    itinerary.append({
        "day_range": f"Day 1-{flight_day_Madrid_Dublin}",
        "place": "Madrid"
    })
    # Dublin: from flight_day_Madrid_Dublin to flight_day_Dublin_Tallinn (Day 4-6)
    itinerary.append({
        "day_range": f"Day {flight_day_Madrid_Dublin}-{flight_day_Dublin_Tallinn}",
        "place": "Dublin"
    })
    # Tallinn: from flight_day_Dublin_Tallinn to total_days (Day 6-7)
    itinerary.append({
        "day_range": f"Day {flight_day_Dublin_Tallinn}-{total_days}",
        "place": "Tallinn"
    })

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()