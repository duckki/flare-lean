function affine(value::Float64, gain::Float64, offset::Float64)
    return value * gain + offset
end

function calibrate(values::Vector{Float64}, gains::Vector{Float64}, offsets::Vector{Float64})
    output = zeros(Float64, length(values))
    for i in 1:length(values)
        output[i] = affine(values[i], gains[i], offsets[i])
    end
    return output
end
