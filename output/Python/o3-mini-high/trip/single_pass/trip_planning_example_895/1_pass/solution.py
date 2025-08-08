Given an ordered list of cities and their durations,
    compute the day ranges for each segment taking into account that each flight day 
    is counted for both the departing and arriving city.
    The first city starts on Day 1 and for each subsequent city the start day is the same 
    as the previous segment's end day.
    Returns a list of tuples: (city, start_day, end_day)