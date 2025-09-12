for h in range(num_houses):
    house_num = h + 1
    name_idx = model.eval(name_ph[h]).as_long()
    name = names_list[name_idx]
    vacation_idx = model.eval(vacation_ph[h]).as_long()
    vacation = vacations_list[vacation_idx]
    education_idx = model.eval(education_ph[h]).as_long()
    education = educations_list[education_idx]
    color_idx = model.eval(color_ph[h]).as_long()
    color = colors_list[color_idx]
    phone_idx = model.eval(phone_ph[h]).as_long()
    phone = phone_models_list[phone_idx]
    food_idx = model.eval(food_ph[h]).as_long()
    food = foods_list[food_idx]
    rows.append([str(house_num), name, vacation, education, color, phone, food])