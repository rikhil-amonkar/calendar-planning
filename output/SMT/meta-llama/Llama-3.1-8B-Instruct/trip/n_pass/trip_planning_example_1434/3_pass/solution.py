for i in range(2, 23):
    s.add(day[i] == day[i-1] + 1)
    s.add(place[i] == place[i-1])