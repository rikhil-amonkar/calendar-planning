Given an order of friend meetings (tuple of friend dicts),
    compute the meeting start and end times accounting for travel and waiting.
    Returns a tuple (itinerary, finish_time) if the schedule is feasible;
    otherwise returns None.
    The itinerary is a list of meeting events.