import json

def main():
    # Input parameters
    total_days = 12
    required_naples_days = 3
    required_seville_days = 4
    required_milan_days = 7
    seville_show_start = 9
    seville_show_end = 12

    # Direct flights available:
    # - Naples <-> Milan
    # - Milan <-> Seville
    # (No direct flight between Naples and Seville)
    
    # We choose the following sequence: Naples -> Milan -> Seville.
    # With the given rule that when flying on a day, the day counts for both departure and arrival,
    # we design the itinerary as follows:
    #
    # 1. Start in Naples. We need a total of 3 days in Naples.
    #    We choose days 1 and 2 in Naples.
    # 2. Fly from Naples to Milan on day 3. This day is counted for both Naples and Milan.
    #    Naples: days 1, 2, and 3 => 3 days total.
    # 3. Stay in Milan from day 3 through day 9.
    #    Milan: day 3 (arrival day overlap) plus days 4,5,6,7,8, and flight day 9.
    #    This gives 7 days in Milan.
    # 4. Fly from Milan to Seville on day 9.
    #    This day is counted in both Milan and Seville.
    # 5. Stay in Seville from day 9 through day 12.
    #    Seville: day 9 (arrival day overlap) plus days 10, 11, and 12.
    #    This gives 4 days in Seville and ensures attendance at the annual show from day 9 to 12.
    
    # Derived day ranges for each city
    naples_day_range = "1-3"   # Days 1,2: solely in Naples; Day 3: overlap flight to Milan
    milan_day_range = "3-9"    # Day 3: arrival from Naples; days 4-8: in Milan; Day 9: overlap flight to Seville
    seville_day_range = "9-12" # Day 9: arrival from Milan; days 10-12: in Seville

    # Prepare the itinerary result as a JSON-formatted list of dictionaries with day_range and place.
    itinerary = [
        {"day_range": naples_day_range, "place": "Naples"},
        {"day_range": milan_day_range, "place": "Milan"},
        {"day_range": seville_day_range, "place": "Seville"}
    ]

    # Output the itinerary in JSON format
    print(json.dumps(itinerary))

if __name__ == '__main__':
    main()