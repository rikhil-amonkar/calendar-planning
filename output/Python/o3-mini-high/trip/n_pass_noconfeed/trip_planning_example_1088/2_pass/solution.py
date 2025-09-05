Given an itinerary order (list of cities in order),
    compute a mapping of each city to its (start, finish) day.
    The rule is:
       start[0] = 1
       finish = start + duration – 1
       start[i+1] = finish[i]