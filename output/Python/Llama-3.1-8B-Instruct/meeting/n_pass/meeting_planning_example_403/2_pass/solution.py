def calculate_travel_time(start_location, end_location):
    travel_time = travel_distances.get((start_location, end_location), travel_distances.get((end_location, start_location)))
    if travel_time is None:
        return datetime.timedelta(minutes=0)
    return datetime.timedelta(minutes=travel_time)