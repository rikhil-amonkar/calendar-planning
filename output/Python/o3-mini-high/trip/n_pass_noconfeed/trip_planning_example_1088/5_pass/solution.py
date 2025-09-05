Given an itinerary (a list of cities in order) and a dictionary 'durations'
    that maps each city to its duration, this function computes and returns
    a dictionary mapping each city to a tuple (start_day, finish_day).

    The rules are:
        - The first city's start_day is 1.
        - For each city, finish_day = start_day + duration - 1.
        - The next city's start_day is equal to the finish_day of the previous city.