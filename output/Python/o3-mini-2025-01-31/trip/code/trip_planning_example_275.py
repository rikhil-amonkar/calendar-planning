import json

def compute_itinerary():
    # Trip constraints as input variables
    total_days = 14
    # Each tuple is (city, required_total_days)
    # Note: The required days are the number of days counted in that city,
    # including the day when you fly into that city (which counts for both departure and arrival).
    # The cities are chosen in an order that respects the direct flight connections:
    # Direct flights: Vilnius <-> Split, Split <-> Madrid, Madrid <-> Santorini.
    # Thus a correct ordering is: Vilnius, Split, Madrid, Santorini.
    cities = [("Vilnius", 4), ("Split", 5), ("Madrid", 6), ("Santorini", 2)]
    
    # The rule is: if you fly from city A to city B on day X,
    # then day X is counted towards both city A and city B.
    # This overlapping day helps to meet the total 14-day trip requirement.
    #
    # Let the flight from city A to city B be on the last day of A.
    # Then for a city with a required duration D, if you start on day S,
    # you must finish on day (S + D - 1). And then the next city starts on that same day.
    
    itinerary = []
    current_day = 1
    for i, (city, duration) in enumerate(cities):
        end_day = current_day + duration - 1
        itinerary.append({"day_range": f"{current_day}-{end_day}", "place": city})
        if i < len(cities) - 1:
            # Next city starts on the same day as the flight day (overlap)
            current_day = end_day
    
    # Ensure the total trip ends on day 14 (it will, if we use overlapping flight days).
    # The computed itinerary:
    # Vilnius: Day 1 to 4 (4 days)
    # Split: Day 4 to 8 (5 days, with Day 4 overlapped)
    # Madrid: Day 8 to 13 (6 days, with Day 8 overlapped)
    # Santorini: Day 13 to 14 (2 days, with Day 13 overlapped)
    #
    # Conference attendance in Santorini on day 13 and 14 is naturally satisfied.
    
    return itinerary

def main():
    itinerary = compute_itinerary()
    # Output the result as JSON-formatted string
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()