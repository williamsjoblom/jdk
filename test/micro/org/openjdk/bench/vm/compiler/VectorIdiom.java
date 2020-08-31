/*
 * Copyright (c) 2020, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package org.openjdk.bench.vm.compiler;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.*;

import java.util.concurrent.TimeUnit;
import java.util.Random;

@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
public abstract class VectorIdiom {
  @Param({"2", "4", "8", "16", "32", "64", "128"})
    public int COUNT;

    private static byte[] bytesA;

    private static Random r = new Random();

    @Setup
    public void init() {
        bytesA = new byte[COUNT];
        r.nextBytes(bytesA);
    }

    @Benchmark
    public int stringHashCodeWrap() {
        return stringHashCodea(bytesA);
    }

    public int stringHashCodea(byte[] a) {
        int h = 0;
        for (int i = 0; i < a.length; i++) {
            h = h*31 + (a[i] & 0xff);
        }
        return h;
    }

    @Fork(value = 1, jvmArgsPrepend = {
            "-XX:+SuperWordPolynomial",
            "-XX:SuperWordPolynomialWidth=16"
        })
    public static class WithXMMSuperword extends VectorIdiom { }

    @Fork(value = 1, jvmArgsPrepend = {
      "-XX:+SuperWordPolynomial",
      "-XX:SuperWordPolynomialWidth=32"
    })
    public static class WithYMMSuperword extends VectorIdiom { }

    @Fork(value = 1, jvmArgsPrepend = {
            "-XX:-SuperWordPolynomial"})
    public static class XNoSuperword extends VectorIdiom { }

}
