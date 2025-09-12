fid = model.evaluate(friend_idx[i])
if fid.as_long() != 9:
    j = fid.as_long()
    st = model.evaluate(start_time[i]).as_long()
    et = model.evaluate(end_time[i]).as_long()
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