import json

def compute_itinerary():
    # Input parameters
    total_days = 11
    
    # Desired durations (as if counting each flight day in both cities)
    seville_days = 6
    paris_days = 2
    krakow_days = 5
    # Workshop constraint: must be in Krakow on a day between 1 and 5.
    
    # The sum of desired durations is 6+2+5 = 13 days.
    # Since we have only 11 days of travel, there must be 2 overlapping flight days.
    # With available direct flights only between:
    #   Krakow <-> Paris and Paris <-> Seville,
    # the only feasible sequence is:
    #   Krakow -> Paris -> Seville.
    
    # Strategy:
    # We'll set the flight from Krakow to Paris on a day such that that day is counted in both Krakow and Paris.
    # Similarly, the flight from Paris to Seville will occur on a day counted in both Paris and Seville.
    #
    # Let:
    #   Flight from Krakow to Paris occur on day X.
    #   Flight from Paris to Seville occur on day Y.
    #
    # Counting the days:
    #   Krakow: from day 1 to day X => X days (and we need krakow_days = 5)
    #   Paris: from day X to day Y => (Y - X + 1) days (we need paris_days = 2)
    #   Seville: from day Y to total_days => (total_days - Y + 1) days (we need seville_days = 6)
    #
    # We get:
    #   X = 5 (to have 5 days in Krakow, including the flight day)
    #   Y - 5 + 1 = 2  --> Y = 6
    #   total_days - 6 + 1 = 6  --> 11 - 6 + 1 == 6, which is correct.
    #
    # Also, workshop in Krakow must occur between day 1 and day 5.
    # With X = 5, we are in Krakow on day 5, so the workshop requirement is satisfied.

    flight_from_krakow_day = 5  # on day 5, traveler flies from Krakow to Paris (overlap on day 5)
    flight_from_paris_day = 6   # on day 6, traveler flies from Paris to Seville (overlap on day 6)
    
    # Define the day ranges for each city.
    # Krakow: days 1 to flight_from_krakow_day (inclusive)
    krakow_range = f"1-{flight_from_krakow_day}"
    # Paris: from flight_from_krakow_day to flight_from_paris_day (inclusive)
    paris_range = f"{flight_from_krakow_day}-{flight_from_paris_day}"
    # Seville: from flight_from_paris_day to total_days (inclusive)
    seville_range = f"{flight_from_paris_day}-{total_days}"
    
    itinerary = [
        {"day_range": krakow_range, "place": "Krakow"},
        {"day_range": paris_range, "place": "Paris"},
        {"day_range": seville_range, "place": "Seville"}
    ]
    
    return itinerary

if __name__ == "__main__":
    itinerary = compute_itinerary()
    # Output the result as a JSON-formatted dictionary (list of dicts)
    print(json.dumps(itinerary, indent=2))