Given an ordered tuple of cities, compute the itinerary segments.
    Each segment is a tuple (city, start_day, end_day).
    The flight day is counted for both the previous and the next city.
    Calculation:
      For the first city: start day = 1, end day = 1 + duration - 1.
      For each subsequent city, start day = previous segment's end day,
      end day = start day + (duration) - 1.