fid = friend_idx[i]
if fid != 9:
    j = fid
    st = start_time[i]
    et = end_time[i]
    loc_idx = friends[j]['location']
    loc_name = locations_names[loc_idx]
    name = friends[j]['name']
    def to_time_str(m):
        h = m // 60
        mm = m % 60
        return f"{h}:{mm:02d}"
    start_str = to_time_str(st)
    end_str = to_time_str(et)
    itinerary.append({
        "action": "meet",
        "location": loc_name,
        "person": name,
        "start_time": start_str,
        "end_time": end_str
    })