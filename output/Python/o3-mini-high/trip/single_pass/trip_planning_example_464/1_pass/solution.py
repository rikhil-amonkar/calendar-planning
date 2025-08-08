Given a route (a tuple of city names in order), compute the itinerary segments.
    On the first city, start day is 1.
    For every subsequent city, the start day equals the previous segment's end day,
    because if you take a flight on that day you are present in both cities.
    Returns a list of segments as dicts with keys: "place", "start", "end".