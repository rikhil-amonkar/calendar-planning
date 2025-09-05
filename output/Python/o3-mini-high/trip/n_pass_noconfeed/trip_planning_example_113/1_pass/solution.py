#!/usr/bin/env python3
import json

def main():
    # Input variables: total trip days and required days in each city.
    total_days = 12
    required_naples = 3
    required_milan = 7
    required_seville = 4

    # Constraint: There is an annual show in Seville from day 9 to day 12.
    show_start = 9
    show_end = 12  # This is equal to total_days, as required_seville is 4 days exactly.

    # We plan the trip in three segments: Naples -> Milan -> Seville,
    # and we only use direct flights (allowed: Naples<->Milan and Milan<->Seville).
    # When flying on a day, that day counts in both the departure and arrival city.
    #
    # Let the flight from Naples to Milan occur on day X.
    # Since we need 3 days in Naples, we set the flight day for Naples->Milan to day 3.
    flight_day_naples_to_milan = required_naples  # Day 3
    #
    # Now, for Milan we need a total of 7 days. Milan gets:
    # - the flight day from Naples (day 3)
    # - (full days between flights) from day (flight_day_naples_to_milan+1) to day (flight_day_milan_to_seville-1)
    # - the flight day to Seville (flight_day_milan_to_seville)
    #
    # Total Milan days = 1 + (flight_day_milan_to_seville - flight_day_naples_to_milan - 1) + 1
    # => flight_day_milan_to_seville - flight_day_naples_to_milan + 1 = required_milan
    # Solve for flight_day_milan_to_seville:
    flight_day_milan_to_seville = flight_day_naples_to_milan + required_milan - 1  # 3 + 7 - 1 = 9

    # To attend the annual show in Seville, we must be in Seville from day 9 to day 12.
    # Our flight from Milan to Seville is on day 9 which then counts for Seville too.
    if flight_day_milan_to_seville != show_start:
        raise ValueError("The flight day into Seville does not match the show's start day.")

    # For Seville, stay from flight_day_milan_to_seville through day 12.
    # Seville days will be: day 9 (overlap flight day) and days 10, 11, 12.
    # Total Seville days = 1 + (total_days - flight_day_milan_to_seville) = 1 + (12 - 9) = 4

    # Construct the itinerary segments:
    # Note: The flight day is included in both the preceding and subsequent city stays.
    itinerary = [
        {
            "day_range": "Day 1-{}".format(flight_day_naples_to_milan),
            "place": "Naples"
        },
        {
            "day_range": "Day {}-{}".format(flight_day_naples_to_milan, flight_day_milan_to_seville),
            "place": "Milan"
        },
        {
            "day_range": "Day {}-{}".format(flight_day_milan_to_seville, total_days),
            "place": "Seville"
        }
    ]

    result = {"itinerary": itinerary}

    # Output the result as a JSON-formatted dictionary.
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()