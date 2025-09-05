Given an itinerary (list of cities, in order)
    and a dictionary 'durations' that maps each city to its duration,
    compute a mapping of each city to its (start_day, finish_day).
    
    The rules are:
      • start_day for the first city is 1.
      • finish_day = start_day + duration - 1.
      • start_day for the next city equals the finish_day of the previous city.