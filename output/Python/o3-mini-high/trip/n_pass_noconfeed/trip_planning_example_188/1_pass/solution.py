#!/usr/bin/env python3
import json

def main():
    # Input constraints and parameters
    total_days = 12
    brussels_days = 2   # Brussels has conference on Day 1 and Day 2
    barcelona_days = 7
    split_days = 5

    # Available direct flights:
    # Brussels <-> Barcelona and Barcelona <-> Split.
    # Because of this, the only viable route that covers all cities is:
    # Brussels -> Barcelona -> Split
    #
    # Note on flight transitions:
    # If you fly on day X, that day is counted for both the departure and arrival cities.
    # Thus the total calendar days is:
    #   (brussels_days + barcelona_days + split_days) - (number of flight transitions)
    # For three cities, there are 2 transitions.
    #
    # Check feasibility:
    required_total = brussels_days + barcelona_days + split_days
    num_transitions = 2  # Brussels->Barcelona and Barcelona->Split
    if required_total - num_transitions != total_days:
        raise ValueError("The given constraints do not sum up to the total number of days when accounting for flight transitions.")

    # Define the cities and their required presence days.
    # The itinerary segments will use overlapping days at transitions.
    # The plan is:
    # - Brussels: Day 1 to Day 2 (conference days, with Day 2 being the transition day)
    # - Barcelona: Day 2 to Day 8 (includes Day 2 arrival and Day 8 departure transition)
    # - Split: Day 8 to Day 12 (includes Day 8 as arrival flight day)
    cities = [("Brussels", brussels_days), ("Barcelona", barcelona_days), ("Split", split_days)]

    itinerary = []
    current_day = 1
    for city, days_required in cities:
        start_day = current_day
        # Compute end day by adding the required days minus one.
        end_day = start_day + days_required - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # For subsequent cities, the flight transition day is shared.
        current_day = end_day

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()