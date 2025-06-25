for i in range(num_time_slots):
    for j in range(num_time_slots):
        if time_slots[j].split('-')[0] < time_slots[i].split('-')[0]:
            s.add(Implies(x[friends.index('Andrew')*6 + locations.index(time_slots[i].split('-')[0])], Not(x[friends.index('Andrew')*6 + locations.index(time_slots[j].split('-')[0])])))