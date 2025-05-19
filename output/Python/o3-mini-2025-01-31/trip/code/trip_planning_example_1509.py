import json

def compute_itinerary():
    # Define the itinerary as a list of cities in the order that satisfies all constraints.
    # We have chosen the following order:
    #   1) Lyon (4 days)
    #   2) Paris (5 days)   --> friend visit possible (days 4-8)
    #   3) Copenhagen (5 days)
    #   4) Santorini (2 days)  --> relatives visit (days 12-13)
    #   5) Oslo (5 days)
    #   6) Krakow (2 days)   --> workshop (days 17-18)
    #   7) Helsinki (5 days) --> friend meet (days 18-22)
    #   8) Warsaw (2 days)
    #   9) Riga (2 days)     --> wedding (days 23-24)
    #  10) Tallinn (2 days)
    #
    # Direct flight validations:
    #   Lyon -> Paris: "Lyon and Paris"
    #   Paris -> Copenhagen: "Paris and Copenhagen"
    #   Copenhagen -> Santorini: "Copenhagen and Santorini"
    #   Santorini -> Oslo: "from Santorini to Oslo"
    #   Oslo -> Krakow: "Oslo and Krakow"
    #   Krakow -> Helsinki: "Krakow and Helsinki"
    #   Helsinki -> Warsaw: "Helsinki and Warsaw"
    #   Warsaw -> Riga: "Warsaw and Riga"
    #   Riga -> Tallinn: "from Riga to Tallinn"
    
    # Define the cities with required durations.
    itinerary_cities = [
        {"place": "Lyon",      "duration": 4},
        {"place": "Paris",     "duration": 5},
        {"place": "Copenhagen","duration": 5},
        {"place": "Santorini", "duration": 2},
        {"place": "Oslo",      "duration": 5},
        {"place": "Krakow",    "duration": 2},
        {"place": "Helsinki",  "duration": 5},
        {"place": "Warsaw",    "duration": 2},
        {"place": "Riga",      "duration": 2},
        {"place": "Tallinn",   "duration": 2},
    ]
    
    # Compute start and end days according to:
    # For the first city, start day is 1.
    # For subsequent cities, if the previous city ended on day X,
    # then the next city starts on day X (flight day counted in both).
    itinerary = []
    current_start = 1
    for city in itinerary_cities:
        duration = city["duration"]
        # End day is start + duration - 1 (because the start day counts fully)
        current_end = current_start + duration - 1
        day_range = f"{current_start}-{current_end}"
        itinerary.append({"day_range": day_range, "place": city["place"]})
        # Next city starts on the same day as this city's end day (flight day overlap)
        current_start = current_end

    return itinerary

def main():
    itinerary = compute_itinerary()
    # Output the itinerary as JSON.
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()