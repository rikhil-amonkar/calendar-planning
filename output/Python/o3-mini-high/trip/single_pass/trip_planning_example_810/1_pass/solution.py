Given an ordering of cities, compute the day ranges for each city.
    The rule is:
      - For the first city, start on day 1.
      - For each city, the range is [start, start + duration - 1].
      - When flying from city A to city B on the same day,
        that day is double-counted (it is the finish day for A and the start day for B).