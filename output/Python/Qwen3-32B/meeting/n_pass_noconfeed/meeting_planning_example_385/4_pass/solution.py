def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{int(hours):02d}:{int(mins):02d}"