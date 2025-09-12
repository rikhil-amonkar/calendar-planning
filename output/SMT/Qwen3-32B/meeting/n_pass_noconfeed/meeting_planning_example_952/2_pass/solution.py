def get_travel_time(loc1, loc2):
    if (loc1, loc2) in travel_times:
        return travel_times[(loc1, loc2)]
    elif (loc2, loc1) in travel_times:
        return travel_times[(loc2, loc1)]
    else:
        raise KeyError(f"Travel time between {loc1} and {loc2} is not defined.")