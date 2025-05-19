import json

def compute_itinerary():
    # Input parameters from the problem
    total_days = 12
    stay_dublin = 2
    stay_riga = 5
    stay_vilnius = 7
    
    # The available direct flights:
    # - Dublin <-> Riga
    # - Riga -> Vilnius
    # Note: A flight day counts for both the departure and arrival cities.
    # 
    # We need to account for the fact that the sum of the individual city stays is 2 + 5 + 7 = 14 days
    # while the itinerary length is 12 days. This difference of 2 days is due to 2 flight days that are counted in two cities.
    # 
    # We plan the itinerary in order: Dublin -> Riga -> Vilnius.
    # We decide to fly from Dublin to Riga on an early flight day and then from Riga to Vilnius on another flight day.
    #
    # The reasoning:
    # - Dublin: To have 2 days in Dublin (including a flight day), we can start with 1 full day in Dublin and then
    #   fly on day 2 so that day 2 counts for both Dublin and Riga.
    # - Riga: With the flight day from Dublin to Riga (day 2) included, we need 4 additional days in Riga
    #   (days 3, 4, 5, and 6). We then take the second flight on day 6 from Riga to Vilnius.
    #   This ensures Riga is accounted for on days 2, 3, 4, 5, and 6.
    # - Vilnius: The flight day from Riga to Vilnius (day 6) counts as one day in Vilnius.
    #   To reach the required 7 days, we then spend days 7 through 12 entirely in Vilnius.
    
    # Calculate day boundaries:
    # Dublin: day 1 (full day) and day 2 (flight day) => "1-2"
    dublin_day_start = 1
    dublin_day_end = 2  # flight day
    
    # Riga: receives from flight on day 2 then full days on 3,4,5 and lastly day6 with flight to Vilnius.
    riga_day_start = dublin_day_end
    # To get total 5 days in Riga, because we already count day2, we need 4 additional days: days 3,4,5,6.
    riga_day_end = 6
    
    # Vilnius: flight day on day 6 plus full days from 7 to 12.
    vilnius_day_start = riga_day_end
    vilnius_day_end = total_days  # 12
    
    itinerary = [
        {"day_range": f"{dublin_day_start}-{dublin_day_end}", "place": "Dublin"},
        {"day_range": f"{riga_day_start}-{riga_day_end}", "place": "Riga"},
        {"day_range": f"{vilnius_day_start}-{vilnius_day_end}", "place": "Vilnius"}
    ]
    
    # Return the JSON string representing the itinerary
    return json.dumps(itinerary, indent=2)

if __name__ == "__main__":
    plan = compute_itinerary()
    print(plan)